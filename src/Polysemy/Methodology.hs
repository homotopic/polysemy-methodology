{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -fplugin=Polysemy.Plugin #-}
module Polysemy.Methodology where

import Control.Monad
import Colog.Polysemy as C
import Polysemy
import Polysemy.KVStore
import Polysemy.Input
import Polysemy.Output
import Polysemy.Several
import Polysemy.Trace

-- | A `Methodology` generalises a semantic process from `b` to `c`.
data Methodology b c m a where
  Process :: b -> Methodology b c m c

makeSem ''Methodology

-- | Run a `Methodology` using a pure function.
runMethodologyPure :: forall b c r a. (b -> c) -> Sem (Methodology b c ': r) a -> Sem r a 
runMethodologyPure f = interpret \case
  Process b -> return $ f b

-- | Run a `Methodology' using a monadic function with effects in `r`.
runMethodologySem :: forall b c r a. (b -> Sem r c) -> Sem (Methodology b c ': r) a -> Sem r a
runMethodologySem f = interpret \case
  Process b -> f b

-- | Cut a `Methodology` into two pieces at a midpoint.
cutMethodology :: forall b c d r a.
                  Members '[ Methodology b c
                           , Methodology c d] r
               => Sem (Methodology b d ': r) a
               -> Sem r a
cutMethodology = interpret \case
  Process b -> process @b @c b >>= process @c @d

-- | Cut a `Methodology` into three pieces using two cuts.
cutMethodology3 :: forall b c d e r a.
                   Members '[ Methodology b c
                            , Methodology c d
                            , Methodology d e] r
               => Sem (Methodology b e ': r) a
               -> Sem r a
cutMethodology3 = interpret \case
  Process b -> process @b @c b >>= process @c @d >>= process @d @e

-- | Divide a `Methodology` into two components using a `Methodology` that accepts a pair.`
divideMethodology :: forall b c c' d r a.
                     Members '[ Methodology b c
                              , Methodology b c'
                              , Methodology (c, c') d] r
                  => Sem (Methodology b d ': r) a
                  -> Sem r a
divideMethodology = interpret \case
  Process b -> do
    c  <- process @b @c  b
    c' <- process @b @c' b
    process @(c, c') @d (c, c')

-- | Decide between two `Methodology`s using a `Methodology` that computes an `Either`.
decideMethodology :: forall b c c' d r a.
                     Members '[ Methodology b (Either c c')
                              , Methodology c  d
                              , Methodology c' d
                              ] r
                  => Sem (Methodology b d ': r) a
                  -> Sem r a
decideMethodology = interpret \case
  Process b -> do
    k <- process @b @(Either c c') b
    case k of
      Left c   -> process @c  @d c
      Right c' -> process @c' @d c'

-- | Tee the output of a `Methodology`, introducing a new `Output` effect to be handled.
teeMethodologyOutput :: forall b c r a.
                  Members '[Output c, Methodology b c] r
               => Sem r a
               -> Sem r a
teeMethodologyOutput = intercept \case
  Process b -> do
    k <- process @b @c b
    output @c k
    return k

-- | Make a `Methodology` depend on an additional input, introducing a new `Input` effect to be handled.
plugMethodologyInput :: forall b c d r a.
                        Members '[Input b, Methodology (b, c) d] r
                     => Sem (Methodology c d ': r) a
                     -> Sem r a
plugMethodologyInput = interpret \case
  Process b -> do
    k <- input @b
    process @(b, c) @d (k, b)

-- | Run a `Methodology` as a `KVStore`, using the input as a key and the output as the value.
runMethodologyAsKVStore :: forall k v r a.
                           Members '[KVStore k v] r
                        => Sem (Methodology k (Maybe v) ': r) a
                        -> Sem r a
runMethodologyAsKVStore = interpret \case
  Process k -> lookupKV k

-- | Run a `Methodology` as a `KVStore`, with a default value for lookup failure.
runMethodologyAsKVStoreWithDefault :: forall k v r a.
                                      Members '[KVStore k v] r
                                   => v
                                   -> Sem (Methodology k v ': r) a
                                   -> Sem r a
runMethodologyAsKVStoreWithDefault d = interpret \case
  Process k -> do
    z <- lookupKV k
    case z of 
      Just a -> return a
      Nothing -> return d

-- | Decompose a `Methodology` into several components to be recombined. This is `cutMethodology` specialised to `HList`.
decomposeMethodology :: forall b f c r a.
                        Members ' [Methodology b (HList f)
                                 , Methodology (HList f) c] r
                     => Sem (Methodology b c ': r) a
                     -> Sem r a
decomposeMethodology = cutMethodology @b @(HList f) @c

-- | Decompose a `Methodology` into several components over three sections with two cuts.
decomposeMethodology3 :: forall b f g c r a.
                         Members '[ Methodology b (HList f)
                                  , Methodology (HList f) (HList g)
                                  , Methodology (HList g) c] r
                      => Sem (Methodology b c ': r) a
                      -> Sem r a
decomposeMethodology3 = cutMethodology3 @b @(HList f) @(HList g) @c

-- | Factor a `Methodology` decomposed over an `HList` in the result by a `Methodology` to the first variable.
separateMethodologyInitial :: forall b x xs r a.
                              Members '[ Methodology b (HList xs)
                                       , Methodology b x] r
                           => Sem (Methodology b (HList (x ': xs)) ': r) a
                           -> Sem r a
separateMethodologyInitial = interpret \case
  Process b -> do
    k   <- process @b @x b
    k'  <- process @b @(HList xs) b
    return $ k ::: k'

-- | Finish an `HList` separated `Methodology` by consuming it for no effect.
endMethodologyInitial :: Sem (Methodology b (HList '[]) ': r) a
                      -> Sem r a
endMethodologyInitial = interpret \case
  Process _ -> return HNil

-- | Factor a `Methodology` decomposed over an `HList` in the source by a `Methodology` from the first variable. Assumes the result is a `Monoid`.
separateMethodologyTerminal :: forall x c xs r a.
                               (Monoid c,
                               Members '[ Methodology (HList xs) c
                                        , Methodology x c] r)
                            => Sem (Methodology (HList (x ': xs)) c ': r) a
                            -> Sem r a
separateMethodologyTerminal = interpret \case
  Process (b ::: bs) -> do
    k   <- process @x @c b
    k'  <- process @(HList xs) @c bs
    return $ k <> k'

-- | Finalise an `HList` separated `Methodology` in the source by returning the `Monoid` unit.
endMethodologyTerminal :: Monoid c
                       => Sem (Methodology (HList '[]) c ': r) a
                       -> Sem r a
endMethodologyTerminal = interpret \case
  Process _ -> return mempty

-- | Run a `Methodology (f b) (f c)` by way of a `Methodology b c`. Note that
-- `f` must be `Traversable`.
fmapMethodology :: forall f b c r a.
                 ( Members '[Methodology b c] r
                 , Traversable f)
                => Sem (Methodology (f b) (f c) ': r) a
                -> Sem r a
fmapMethodology = interpret \case
  Process b -> traverse (process @b @c) b

-- | Run a `Methodology (f (g b)) (f (g c))` by way of a `Methodology b c`. Note that
-- `f` and `g` must be `Traversable`.
fmap2Methodology :: forall f g b c r a.
                  ( Members '[Methodology b c] r
                  , Traversable f, Traversable g)
                 => Sem (Methodology (f (g b)) (f (g c)) ': Methodology (g b) (g c) ': r) a
                 -> Sem r a
fmap2Methodology = fmapMethodology @g @b @c . fmapMethodology @f @(g b) @(g c)

-- | Run a `Methodology (f b) (f c)` by way of a `Methodology b (f c)`. Note that
-- `f` must be both `Traversable` and `Monad`.
bindMethodology :: forall f b c r a.
                 ( Members '[Methodology b (f c)] r
                 , Traversable f, Monad f)
                => Sem (Methodology (f b) (f c) ': r) a
                -> Sem r a
bindMethodology = interpret \case
  Process b -> join <$> traverse (process @b @(f c)) b

-- | Run a `Methodology (t b) (f (t b))` by way of a `Methodology b (f c)`. Note that
-- `t` must be `Traversable` and `f` must be `Applicative`.
traverseMethodology :: forall t f b c r a.
                     ( Members '[Methodology b (f c)] r
                     , Traversable t, Applicative f)
                    => Sem (Methodology (t b) (f (t c)) ': r) a
                    -> Sem r a
traverseMethodology = interpret \case
  Process b -> sequenceA <$> traverse (process @b @(f c)) b

-- | `Trace` a `String` based on the input to a `Methodology`.
traceMethodologyStart :: forall b c r a.
                         Members '[Methodology b c,
                                   Trace] r
                       => (b -> String)
                       -> Sem r a
                       -> Sem r a
traceMethodologyStart f = intercept \case
  Process b -> trace (f b) >> process @b @c b

-- | `Trace` a `String` based on the output to a `Methodology`.
traceMethodologyEnd :: forall b c r a.
                       Members '[Methodology b c,
                                Trace] r
                       => (c -> String)
                       -> Sem r a
                       -> Sem r a
traceMethodologyEnd f = intercept \case
  Process b -> do
    c <- process @b @c b
    trace $ f c
    return c

-- | `Trace` both the start and the end of a `Methodology`.
traceMethodologyAround :: forall b c r a.
                           Members '[Methodology b c,
                                     Trace] r
                       => (b -> String)
                       -> (c -> String)
                       -> Sem r a
                       -> Sem r a
traceMethodologyAround f g = intercept \case
  Process b -> do
    trace $ f b
    c <- process @b @c b
    trace $ g c
    return c

-- | `Log` a type based on the input to a `Methodology`.
logMethodologyStart :: forall b c p r a.
                       Members '[Methodology b c,
                                 Log p] r
                       => (b -> p)
                       -> Sem r a
                       -> Sem r a
logMethodologyStart f = intercept \case
  Process b -> C.log (f b) >> process @b @c b


-- | `Log` a type based on the output to a `Methodology`.
logMethodologyEnd :: forall b c q r a.
                       Members '[Methodology b c,
                                Log q] r
                       => (c -> q)
                       -> Sem r a
                       -> Sem r a
logMethodologyEnd f = intercept \case
  Process b -> do
    c <- process @b @c b
    C.log $ f c
    return c

-- | `Log` both the start and the end of a `Methodology`.
logMethodologyAround :: forall b c p q r a.
                           Members '[Methodology b c,
                                     Log p
                                    , Log q] r
                       => (b -> p)
                       -> (c -> q)
                       -> Sem r a
                       -> Sem r a
logMethodologyAround f g = intercept \case
  Process b -> do
    C.log $ f b
    c <- process @b @c b
    C.log $ g c
    return c
