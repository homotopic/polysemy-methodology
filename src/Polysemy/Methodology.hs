{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -fplugin=Polysemy.Plugin #-}

-- |
--   Module     : Polysemy.Methodology
--   License    : MIT
--   Stability  : experimental
--
-- Domain modelling algebra for polysemy.
module Polysemy.Methodology
  ( -- * Definition
    Methodology (..),
    process,

    -- * Eliminators
    runMethodologyPure,
    runMethodologySem,

    -- * Decomposition
    cutMethodology,
    cutMethodology',
    cutMethodology3,
    cutMethodology3',
    divideMethodology,
    divideMethodology',
    decideMethodology,
    decideMethodology',
    decomposeMethodology,
    decomposeMethodology',
    decomposeMethodology3,
    separateMethodologyInitial,
    endMethodologyInitial,
    separateMethodologyTerminal,
    endMethodologyTerminal,

    -- * Simplifcation
    fmapMethodology,
    fmapMethodology',
    fmap2Methodology,
    fmap2Methodology',
    pureMethodology,
    pureMethodology',
    bindMethodology,
    bindMethodology',
    traverseMethodology,
    traverseMethodology',
    mconcatMethodology,
    mconcatMethodology',

    -- * Other Effects
    teeMethodologyOutput,
    plugMethodologyInput,
    runMethodologyAsKVStore,
    runMethodologyAsKVStoreWithDefault,
    runMethodologyMappendPure,
    runMethodologyMappendSem,

    -- * Tracing
    traceMethodologyStart,
    traceMethodologyEnd,
    traceMethodologyAround,

    -- * Logging
    logMethodologyStart,
    logMethodologyEnd,
    logMethodologyAround,
  )
where

import Colog.Polysemy as C
import Control.Applicative
import Control.Arrow
import Control.Monad
import Polysemy
import Polysemy.Input
import Polysemy.KVStore
import Polysemy.Output
import Polysemy.Several
import Polysemy.Trace

-- | A `Methodology` generalises a semantic process from `b` to `c`.
data Methodology b c m a where
  Process :: b -> Methodology b c m c

makeSem ''Methodology

-- | Run a `Methodology` using a pure function.
--
-- @since 0.1.0.0
runMethodologyPure ::
  forall b c r a.
  -- | A function from b to c.
  (b -> c) ->
  Sem (Methodology b c ': r) a ->
  Sem r a
runMethodologyPure f = interpret \case
  Process b -> return $ f b
{-# INLINE runMethodologyPure #-}

-- | Run a `Methodology' using a monadic function with effects in `r`.
--
-- @since 0.1.0.0
runMethodologySem ::
  forall b c r a.
  -- | A monadic function from b to c using effects in r.
  (b -> Sem r c) ->
  Sem (Methodology b c ': r) a ->
  Sem r a
runMethodologySem f = interpret \case
  Process b -> f b
{-# INLINE runMethodologySem #-}

-- | Cut a `Methodology` into two pieces at a midpoint.
--
-- @since 0.1.0.0
cutMethodology ::
  forall b c d r a.
  Members
    '[ Methodology b c,
       Methodology c d
     ]
    r =>
  -- | Methodology effect to decompose.
  Sem (Methodology b d ': r) a ->
  Sem r a
cutMethodology = interpret \case
  Process b -> process @b @c b >>= process @c @d
{-# INLINE cutMethodology #-}

-- | Reinterpreting version of `cutMethodology`.
--
-- @since 0.1.6.0
cutMethodology' ::
  forall b c d r a.
  -- | Methodology effect to decompose.
  Sem (Methodology b d ': r) a ->
  Sem (Methodology b c ': Methodology c d ': r) a
cutMethodology' = reinterpret2 \case
  Process b -> process @b @c b >>= raise . process @c @d
{-# INLINE cutMethodology' #-}

-- | Cut a `Methodology` into three pieces using two cuts.
--
-- @since 0.1.0.0
cutMethodology3 ::
  forall b c d e r a.
  Members
    '[ Methodology b c,
       Methodology c d,
       Methodology d e
     ]
    r =>
  -- | Methodology effect to decompose.
  Sem (Methodology b e ': r) a ->
  Sem r a
cutMethodology3 = interpret \case
  Process b -> process @b @c b >>= process @c @d >>= process @d @e
{-# INLINE cutMethodology3 #-}

-- | Reinterpreting version of `cutMethodology`.
--
-- @since 0.1.6.0
cutMethodology3' ::
  forall b c d e r a.
  -- | Methodology effect to decompose.
  Sem (Methodology b d ': r) a ->
  Sem (Methodology b c ': Methodology c d ': Methodology d e ': r) a
cutMethodology3' = reinterpret3 \case
  Process b -> process @b @c b >>= raise . process @c @d
{-# INLINE cutMethodology3' #-}

-- | Divide a `Methodology` into two components using a `Methodology` that accepts a pair.`
--
-- @since 0.1.0.0
divideMethodology ::
  forall b c c' d r a.
  Members
    '[ Methodology b c,
       Methodology b c',
       Methodology (c, c') d
     ]
    r =>
  -- | Methodology effect to decompose.
  Sem (Methodology b d ': r) a ->
  Sem r a
divideMethodology = interpret \case
  Process b -> do
    c <- process @b @c b
    c' <- process @b @c' b
    process @(c, c') @d (c, c')
{-# INLINE divideMethodology #-}

-- | Reinterpreting version of `divideMethodology`.
--
-- @since 0.1.6.0
divideMethodology' ::
  forall b c c' d r a.
  Sem (Methodology b d ': r) a ->
  Sem (Methodology b c ': Methodology b c' ': Methodology (c, c') d ': r) a
divideMethodology' = reinterpret3 \case
  Process b -> do
    c <- process @b @c b
    c' <- raise $ process @b @c' b
    raise $ raise $ process @(c, c') @d (c, c')
{-# INLINE divideMethodology' #-}

-- | Decide between two `Methodology`s using a `Methodology` that computes an `Either`.
--
-- @since 0.1.0.0
decideMethodology ::
  forall b c c' d r a.
  Members
    '[ Methodology b (Either c c'),
       Methodology c d,
       Methodology c' d
     ]
    r =>
  -- | `Methodology effect to decompose.
  Sem (Methodology b d ': r) a ->
  Sem r a
decideMethodology = interpret \case
  Process b -> do
    k <- process @b @(Either c c') b
    case k of
      Left c -> process @c @d c
      Right c' -> process @c' @d c'
{-# INLINE decideMethodology #-}

-- | Reinterpreting version of `decideMethodology`.
--
-- @since 0.1.6.0
decideMethodology' ::
  forall b c c' d r a.
  Sem (Methodology b d ': r) a ->
  Sem (Methodology b (Either c c') ': Methodology c d ': Methodology c' d ': r) a
decideMethodology' = reinterpret3 \case
  Process b -> do
    k <- process @b @(Either c c') b
    case k of
      Left c -> raise $ process @c @d c
      Right c' -> raise $ raise $ process @c' @d c'
{-# INLINE decideMethodology' #-}

-- | Tee the output of a `Methodology`, introducing a new `Output` effect to be handled.
--
-- @since 0.1.0.0
teeMethodologyOutput ::
  forall b c r a.
  Members
    '[ Output c,
       Methodology b c
     ]
    r =>
  Sem r a ->
  Sem r a
teeMethodologyOutput = intercept \case
  Process b -> do
    k <- process @b @c b
    output @c k
    return k
{-# INLINE teeMethodologyOutput #-}

-- | Make a `Methodology` depend on an additional input, introducing a new `Input` effect to be handled.
--
-- @since 0.1.0.0
plugMethodologyInput ::
  forall b c d r a.
  Members '[Input b, Methodology (b, c) d] r =>
  Sem (Methodology c d ': r) a ->
  Sem r a
plugMethodologyInput = interpret \case
  Process b -> do
    k <- input @b
    process @(b, c) @d (k, b)
{-# INLINE plugMethodologyInput #-}

-- | Run a `Methodology` as a `KVStore`, using the input as a key and the output as the value.
--
-- @since 0.1.0.0
runMethodologyAsKVStore ::
  forall k v r a.
  Members '[KVStore k v] r =>
  Sem (Methodology k (Maybe v) ': r) a ->
  Sem r a
runMethodologyAsKVStore = interpret \case
  Process k -> lookupKV k
{-# INLINE runMethodologyAsKVStore #-}

-- | Run a `Methodology` as a `KVStore`, with a default value for lookup failure.
--
-- @since 0.1.0.0
runMethodologyAsKVStoreWithDefault ::
  forall k v r a.
  Members '[KVStore k v] r =>
  -- | A default value v.
  v ->
  Sem (Methodology k v ': r) a ->
  Sem r a
runMethodologyAsKVStoreWithDefault d = interpret \case
  Process k -> do
    z <- lookupKV k
    case z of
      Just a -> return a
      Nothing -> return d
{-# INLINE runMethodologyAsKVStoreWithDefault #-}

-- | Run a `Methodology` targetting a `Monoid` without consuming it, pure version. This should probably be considered an
-- anti-pattern, and it's probably better to decompose the inputs fully, but is otherwise sound.
--
-- @since 0.1.8.0
runMethodologyMappendPure ::
  forall b c r a.
  ( Monoid c,
    Members '[Methodology b c] r
  ) =>
  (b -> c) ->
  Sem r a ->
  Sem r a
runMethodologyMappendPure f = intercept \case
  Process b -> (f b <>) <$> process @b @c b
{-# INLINE runMethodologyMappendPure #-}

-- | Run a `Methodology` targetting a `Monoid` without consuming it, `Sem` version. This should probably be considered an
-- anti-pattern, and it's probably better to decompose the inputs fully, but is otherwise sound.
--
-- @since 0.1.8.0
runMethodologyMappendSem ::
  forall b c r a.
  ( Monoid c,
    Members '[Methodology b c] r
  ) =>
  (b -> Sem r c) ->
  Sem r a ->
  Sem r a
runMethodologyMappendSem f = intercept \case
  Process b -> liftA2 (<>) (f b) (process @b @c b)
{-# INLINE runMethodologyMappendSem #-}

-- | Decompose a `Methodology` into several components to be recombined. This is `cutMethodology` specialised to `HList`.
--
-- @since 0.1.0.0
decomposeMethodology ::
  forall b f c r a.
  Members
    '[ Methodology b (HList f),
       Methodology (HList f) c
     ]
    r =>
  Sem (Methodology b c ': r) a ->
  Sem r a
decomposeMethodology = cutMethodology @b @(HList f) @c
{-# INLINE decomposeMethodology #-}

-- | Reinterpreting version of `decomposeMethodology`.
--
-- @since 0.1.6.0
decomposeMethodology' ::
  forall b f c r a.
  Sem (Methodology b c ': r) a ->
  Sem (Methodology b (HList f) ': Methodology (HList f) c ': r) a
decomposeMethodology' = cutMethodology' @b @(HList f) @c
{-# INLINE decomposeMethodology' #-}

-- | Decompose a `Methodology` into several components over three sections with two cuts.
--
-- @since 0.1.0.0
decomposeMethodology3 ::
  forall b f g c r a.
  Members
    '[ Methodology b (HList f),
       Methodology (HList f) (HList g),
       Methodology (HList g) c
     ]
    r =>
  Sem (Methodology b c ': r) a ->
  Sem r a
decomposeMethodology3 = cutMethodology3 @b @(HList f) @(HList g) @c
{-# INLINE decomposeMethodology3 #-}

-- | Factor a `Methodology` decomposed over an `HList` in the result by a `Methodology` to the first variable.
--
-- @since 0.1.0.0
separateMethodologyInitial ::
  forall b x xs r a.
  Members
    '[ Methodology b (HList xs),
       Methodology b x
     ]
    r =>
  Sem (Methodology b (HList (x ': xs)) ': r) a ->
  Sem r a
separateMethodologyInitial = interpret \case
  Process b -> do
    k <- process @b @x b
    k' <- process @b @(HList xs) b
    return $ k ::: k'
{-# INLINE separateMethodologyInitial #-}

-- | Finish an `HList` separated `Methodology` by consuming it for no effect.
--
-- @since 0.1.0.0
endMethodologyInitial ::
  Sem (Methodology b (HList '[]) ': r) a ->
  Sem r a
endMethodologyInitial = interpret \case
  Process _ -> return HNil
{-# INLINE endMethodologyInitial #-}

-- | Factor a `Methodology` decomposed over an `HList` in the source by a
-- `Methodology` from the first variable. Assumes the result is a `Monoid`.
--
-- @since 0.1.0.0
separateMethodologyTerminal ::
  forall x c xs r a.
  ( Monoid c,
    Members
      '[ Methodology (HList xs) c,
         Methodology x c
       ]
      r
  ) =>
  Sem (Methodology (HList (x ': xs)) c ': r) a ->
  Sem r a
separateMethodologyTerminal = interpret \case
  Process (b ::: bs) -> do
    k <- process @x @c b
    k' <- process @(HList xs) @c bs
    return $ k <> k'
{-# INLINE separateMethodologyTerminal #-}

-- | Finalise an `HList` separated `Methodology` in the source by returning the `Monoid` unit.
--
-- @since 0.1.0.0
endMethodologyTerminal ::
  Monoid c =>
  Sem (Methodology (HList '[]) c ': r) a ->
  Sem r a
endMethodologyTerminal = interpret \case
  Process _ -> return mempty
{-# INLINE endMethodologyTerminal #-}

-- | Run a `Methodology` (f b) (f c) by way of a `Methodology` b c. Note that
-- `f` must be `Traversable`.
--
-- @since 0.1.2.0
fmapMethodology ::
  forall f b c r a.
  ( Members '[Methodology b c] r,
    Traversable f
  ) =>
  Sem (Methodology (f b) (f c) ': r) a ->
  Sem r a
fmapMethodology = interpret \case
  Process b -> traverse (process @b @c) b
{-# INLINE fmapMethodology #-}

-- | Reinterpreting version of `fmapMethodology`.
--
-- @since 0.1.6.0
fmapMethodology' ::
  forall f b c r a.
  Traversable f =>
  Sem (Methodology (f b) (f c) ': r) a ->
  Sem (Methodology b c ': r) a
fmapMethodology' = raiseUnder >>> fmapMethodology
{-# INLINE fmapMethodology' #-}

-- | Run a `Methodology` (f (g b)) (f (g c))) by way of a `Methodology` b c. Note that
-- `f` and `g` must be `Traversable`.
--
-- @since 0.1.2.0
fmap2Methodology ::
  forall f g b c r a.
  ( Members '[Methodology b c] r,
    Traversable f,
    Traversable g
  ) =>
  Sem (Methodology (f (g b)) (f (g c)) ': r) a ->
  Sem r a
fmap2Methodology = fmapMethodology' @f @(g b) @(g c) >>> fmapMethodology @g @b @c
{-# INLINE fmap2Methodology #-}

-- | Reinterpreting version of `fmap2Methodology`.
--
-- @since 0.1.6.0
fmap2Methodology' ::
  forall f g b c r a.
  (Traversable f, Traversable g) =>
  Sem (Methodology (f (g b)) (f (g c)) ': r) a ->
  Sem (Methodology b c ': r) a
fmap2Methodology' = raiseUnder >>> fmap2Methodology
{-# INLINE fmap2Methodology' #-}

-- | Run a `Methodology` b (f c) in terms of a `Methodology` b c.
--
-- @since 0.1.7.0
pureMethodology ::
  forall f b c r a.
  (Members '[Methodology b c] r, Applicative f) =>
  Sem (Methodology b (f c) ': r) a ->
  Sem r a
pureMethodology = interpret \case
  Process b -> pure <$> process @b @c b
{-# INLINE pureMethodology #-}

-- | Reinterpreting version of `pureMethodology`.
--
-- @since 0.1.7.0
pureMethodology' ::
  forall f b c r a.
  Applicative f =>
  Sem (Methodology b (f c) ': r) a ->
  Sem (Methodology b c ': r) a
pureMethodology' = raiseUnder >>> pureMethodology
{-# INLINE pureMethodology' #-}

-- | Run a `Methodology` (f b) (f c) by way of a `Methodology` b (f c). Note that
-- `f` must be both `Traversable` and `Monad`.
--
-- @since 0.1.2.0
bindMethodology ::
  forall f b c r a.
  ( Members '[Methodology b (f c)] r,
    Traversable f,
    Monad f
  ) =>
  Sem (Methodology (f b) (f c) ': r) a ->
  Sem r a
bindMethodology = interpret \case
  Process b -> join <$> traverse (process @b @(f c)) b
{-# INLINE bindMethodology #-}

-- | Reinterpreting version of `bindMethodology`.
--
-- @since 0.1.6.0
bindMethodology' ::
  forall f b c r a.
  (Traversable f, Monad f) =>
  Sem (Methodology (f b) (f c) ': r) a ->
  Sem (Methodology b (f c) ': r) a
bindMethodology' = raiseUnder >>> bindMethodology
{-# INLINE bindMethodology' #-}

-- | Run a `Methodology` (t b) (f (t b)) by way of a `Methodology` b (f c). Note that
-- `t` must be `Traversable` and `f` must be `Applicative`.
--
-- @since 0.1.2.0
traverseMethodology ::
  forall t f b c r a.
  ( Members '[Methodology b (f c)] r,
    Traversable t,
    Applicative f
  ) =>
  Sem (Methodology (t b) (f (t c)) ': r) a ->
  Sem r a
traverseMethodology = interpret \case
  Process b -> sequenceA <$> traverse (process @b @(f c)) b
{-# INLINE traverseMethodology #-}

-- | Reinterpreting version of `traverseMethodology`.
--
-- @since 0.1.6.0
traverseMethodology' ::
  forall t f b c r a.
  (Traversable t, Applicative f) =>
  Sem (Methodology (t b) (f (t c)) ': r) a ->
  Sem (Methodology b (f c) ': r) a
traverseMethodology' = raiseUnder >>> traverseMethodology
{-# INLINE traverseMethodology' #-}

-- | Run a `Methodology` concatenating the results as a monoid.
--
-- @since 0.1.5.0
mconcatMethodology ::
  forall f b c r a.
  ( Members '[Methodology b c] r,
    Monoid c,
    Traversable f
  ) =>
  Sem (Methodology (f b) c ': r) a ->
  Sem r a
mconcatMethodology = interpret \case
  Process b -> traverse (process @b @c) b >>= return . foldr (<>) mempty
{-# INLINE mconcatMethodology #-}

-- | Reinterpreting version of `mconcatMethodology`.
--
-- @since 0.1.6.0
mconcatMethodology' ::
  forall f b c r a.
  (Monoid c, Traversable f) =>
  Sem (Methodology (f b) c ': r) a ->
  Sem (Methodology b c ': r) a
mconcatMethodology' = raiseUnder >>> mconcatMethodology
{-# INLINE mconcatMethodology' #-}

-- | `Trace` a `String` based on the input to a `Methodology`.
--
-- @since 0.1.3.0
traceMethodologyStart ::
  forall b c r a.
  Members
    '[ Methodology b c,
       Trace
     ]
    r =>
  -- | A function from the input type b to a `String`.
  (b -> String) ->
  Sem r a ->
  Sem r a
traceMethodologyStart f = intercept \case
  Process b -> trace (f b) >> process @b @c b
{-# INLINE traceMethodologyStart #-}

-- | `Trace` a `String` based on the output to a `Methodology`.
--
-- @since 0.1.3.0
traceMethodologyEnd ::
  forall b c r a.
  Members
    '[ Methodology b c,
       Trace
     ]
    r =>
  -- | A function from the output type c to a `String`.
  (c -> String) ->
  Sem r a ->
  Sem r a
traceMethodologyEnd f = intercept \case
  Process b -> do
    c <- process @b @c b
    trace $ f c
    return c
{-# INLINE traceMethodologyEnd #-}

-- | `Trace` both the start and the end of a `Methodology`.
--
-- @since 0.1.3.0
traceMethodologyAround ::
  forall b c r a.
  Members
    '[ Methodology b c,
       Trace
     ]
    r =>
  -- | A function from the input type b to a `String`.
  (b -> String) ->
  -- | A function from the output type c to a `String`.
  (c -> String) ->
  Sem r a ->
  Sem r a
traceMethodologyAround f g = intercept \case
  Process b -> do
    trace $ f b
    c <- process @b @c b
    trace $ g c
    return c
{-# INLINE traceMethodologyAround #-}

-- | `Log` a type based on the input to a `Methodology`.
--
-- @since 0.1.4.0
logMethodologyStart ::
  forall b c p r a.
  Members
    '[ Methodology b c,
       Log p
     ]
    r =>
  -- | A function from the input type b to an event type p.
  (b -> p) ->
  Sem r a ->
  Sem r a
logMethodologyStart f = intercept \case
  Process b -> C.log (f b) >> process @b @c b
{-# INLINE logMethodologyStart #-}

-- | `Log` a type based on the output to a `Methodology`.
--
-- @since 0.1.4.0
logMethodologyEnd ::
  forall b c q r a.
  Members
    '[ Methodology b c,
       Log q
     ]
    r =>
  -- | A function from the input type c to an event type q.
  (c -> q) ->
  Sem r a ->
  Sem r a
logMethodologyEnd f = intercept \case
  Process b -> do
    c <- process @b @c b
    C.log $ f c
    return c
{-# INLINE logMethodologyEnd #-}

-- | `Log` both the start and the end of a `Methodology`.
--
-- @since 0.1.4.0
logMethodologyAround ::
  forall b c p q r a.
  Members
    '[ Methodology b c,
       Log p,
       Log q
     ]
    r =>
  -- | A function from the input type b to an event type p.
  (b -> p) ->
  -- | A function from the output type b to an event type q,
  (c -> q) ->
  Sem r a ->
  Sem r a
logMethodologyAround f g = intercept \case
  Process b -> do
    C.log $ f b
    c <- process @b @c b
    C.log $ g c
    return c
{-# INLINE logMethodologyAround #-}
