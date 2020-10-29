# polysemy-methodology

polysemy-methodology provides an algebra for domain modelling in polysemy.

A simple program might look something like this:

```
prog :: Members '[ Input a
                 , Methodology a b
                 , Output b]
     => Sem r ()
prog = input @a >>= process @a @b >>= output @b
```

That is, this program transforms an `Input a` into an `Output b` by way of a
`Methodology a b` that turns `a` into `b`. We can then type apply `a` and `b`
and connect this to `main`.

If we have a solution readily available, we can consume a `Methodology` by
running one of the interpreters `runMethodologyPure` or `runMethodologySem`.

Otherwise, we can use the other interpreters in this package to break the
problem down into components or branches and solve each section separately.
Each interpreter will produce a new set of `Methodology`s to be solved.

This allows you to work up a solution to a domain problem backwards, by running
the program you intend to solve directly and using holes to guide the
requirements.

## Worked example

A worked example of this approach can be found in the
[flashblast](https://gitlab.com/homotopic-tech/flashblast)
repository. In this we want to take a configuration in dhall,
and process it in some way an output of flashcards.

We might model this as such:

```
import Polysemy
import Polysemy.Input
import Polysemy.Tagged
import Polysemy.Methodology
import Polysemy.Output

-- | A `DeckConfiguration` indicates how we create cards.
data DeckConfiguration

-- | A `CollectionsPackage` indicates.
data CollectionsPackage

-- | The Construction Methodology for flashblast.
data ConstructionMethodology

-- | `flashblast` is a program that takes a `DeckConfiguration` and outputs a `CollectionsPackage`.
flashblast :: Members '[ Tagged DeckConfiguration (Input a)
                       , Tagged ConstructionMethodology (Methodology a b)
                       , Tagged CollectionsPackage (Output b)] r
           => Sem r ()
flashblast = do
  x <- tag @DeckConfiguration input
  k <- tag @ConstructionMethodology $ process x
  tag @CollectionsPackage $ output k
```

Notice that this is an abstract domain model. We have not committed to
a particular representation of any of the three elements of this program.
In fact, the domain model depends only on polysemy libraries, which allows
us to isolate the domain model from anything resembling real code.

We commit to a concrete representation for the config and for
the output only in the main application file, where we iterate over
the decks.

```
-- Config.hs
data Spec =
    Pronunciation   [PronunciationSpec]
  | Excerpt         [ExcerptSpec]
  | BasicReversed   [BasicReversedCard]
  | MinimalReversed [MinimalReversedCard]
    deriving stock Generic
    deriving D.FromDhall
      via D.Codec (D.Field (D.DropPrefix "_")) Spec

makePrisms ''Spec

data Part = Part {
  _outfile :: Path Rel File
, _spec    :: Spec
} deriving Generic
  deriving D.FromDhall
    via D.Codec (D.Field (D.DropPrefix "_")) Part

data Deck = Deck {
  _resourceDirs :: ResourceDirs
, _exportDirs   :: ExportDirs
, _parts        :: [Part]
} deriving stock Generic
  deriving D.FromDhall
    via D.Codec (D.Field (D.DropPrefix "_")) Deck
```

```
-- Main.hs
data Deck = Deck {
  notes :: Map (Path Rel File) Text
, media :: [Path Rel File]
} deriving stock (Eq, Show, Generic)
  deriving Semigroup via GenericSemigroup Deck
  deriving Monoid via GenericMonoid Deck

main = do
  Config.FlashBlast{..} <- D.input D.auto "./index.dhall"
  forM_ _decks $ \x -> do
    flashblast @Config.Deck @Deck
      & runM
```

Here we will be told that we need to satisfy the `Input`, `Output` and
`Methodology` effects.

The Config.Deck is divided into several different specs. We could simply
write one giant function to solve the methodology.

```
soln :: Members '[...] r => Config.Deck -> Sem r Deck
soln = ...

-- runMethodologySem @Config.Deck @Deck soln
```

But this would conflate our concerns - the different specs require different
effects to execute, and having this single function require all effects
wouuld be maintenance should we choose to remove any functionality:

* The `MinimalReversedCard`s and `BasicReversedCard`s are simple
  representations of what the output cards should look like, and so can be
purely transformed.
* `ExcerptSpec`s need to be transformed into cards by way of processing
  the specified video and subtitle track via ffmpeg.
* `PronunciationSpec`s need to be transformed via megaparsec and the
  audio for the extracted words retrieved from a remote API.

What would be nice is if we could reach a point where we can make functions
for each of with their respective effects isolated but without having to
agglomerate all the effects into a single solution function.

It makes sense then to take our `Methodology` and break it down into sub
`Methodology`s that can be reasoned about independently, rather than trying
to satisfy the program with one function built up from parts. This way
we can break the program down using only type applications and interpreters.

The interpreters in this library aree operations that consume a `Methodology`
and turn it into parts.

`cutMethodology` breaks the `Methodology` into two pieces, and will then
require interpreters for each. So if we start with a `Methodology b d`, we
can break it into `Methodology b c` and `Methodology c d`, each of which
will require some solution. This is essentially reverse arrow composition.

```
b -----> d   ===>  (b ---> c), (c ---> d)
```

`divideMethodology` breaks the target into a pair, and connects
the source to both of them, producing three `Methodology`s we need to solve. This is reverse fanout.

```
b ----> d ==> (b ---> c), (b ---> c'), ((c,c') ----> d)
```

`decideMethodology` breaks the source into an `Either`, allowing us to
choose a `Methodology` to run as the result of another `Methodology`
based on the source. This is reverse fanin.

```
b ----> d ===> (b---> Either c c'), (c ---> d), (c ---> d)
```

`decomposeMethodology` is `cutMethodology` specialised to
`HList` as the center argument. This allows us to cut the
`Methodology` into multiple parallel tracks.

```
                /-----c-----\
b ----> d ===> b------d------f
                \-----e-----/
```

Back to our example, we need to decompose our `Config` into
the problems concerning each type of spec, then turn
each of those into a `Deck` of its own, then collect the
produced decks monoidally into the final output.

Dealing with HLists is a little awkward but the approach that
will work is to deal with each strand individually, and use
`separateMethodologyInitial` or `separateMethodologyTerminal`
depending on whether the strand appears before or after the
`HList`, which will separate the element of the `HList` into
its own `Methodology`. Then, decompose this further or solve
it.

```
type DeckSplit = '[Map (Path Rel File) [Config.MinimalReversedCard]
                 , Map (Path Rel File) [Config.BasicReversedCard]
                 , Map (Path Rel File) [Config.ExcerptSpec]
                 , Map (Path Rel File) [Config.PronunciationSpec]
                 ]

type FileMap b = Map (Path b File)

extractParts :: Prism' Config.Spec x -> Config.Deck -> Map (Path Rel File) x
extractParts x = Map.fromList . itoListOf
                  ( Config.parts
                  % itraversed
                  %> reindexed (view Config.outfile) selfIndex
                  % Config.spec
                  % x
                  )



main = do
  Config.FlashBlast{..} <- D.input D.auto "./index.dhall"
  forM_ _decks $ \x -> do
    flashblast @Config.Deck @Deck
      & untag @ConstructionMethodology
      & decomposeMethodology @Config.Deck @DeckSplit @Deck
        -- We pull out `Config.Deck -> (FileMap Rel [Config.MinimalReversedCard]` as its own `Methodology`.
        & separateMethodologyInitial @Config.Deck @(FileMap Rel [Config.MinimalReversedCard])
          -- And then immediately solve it purely.
          & runMethodologyPure (extractParts Config._MinimalReversed)
        -- and do the same for each one in the list.
        & separateMethodologyInitial @Config.Deck @(FileMap Rel [Config.BasicReversedCard])
          & runMethodologyPure (extractParts Config._BasicReversed)
        & separateMethodologyInitial @Config.Deck @(FileMap Rel [Config.ExcerptSpec])
          & runMethodologyPure (extractParts Config._Excerpt)
        & separateMethodologyInitial @Config.Deck @(FileMap Rel [Config.PronunciationSpec])
          & runMethodologyPure (extractParts Config._Pronunciation)
        & endMethodologyInitial
          & separateMethodologyTerminal @(FileMap Rel [Config.MinimalReversedCard]) @Deck
            & runMethodologyPure _
          & separateMethodologyTerminal @(FileMap Rel [Config.BasicReversedCard]) @Deck
            & runMethodologyPure _
          & separateMethodologyTerminal @(FileMap Rel [Config.ExcerptSpec]) @Deck
            & runMethodologySem _
          & separateMethodologyTerminal @(FileMap Rel [Config.PronunciationSpec]) @Deck
            & runMethodologySem _
```

We have left holes that polysemy will now tell us need to be
filled by nice clean `a -> b` or `a -> Sem r b` functions.
Any effects we add here we can deal with after this block, or
we can decompose this even further (see flashblast for details).

## Notes

There are intended to be less boilerplatey ways to deal with
separation, as a very common pattern is simply to separate a
strand out and then immediately solve it, but this library is
early and I didn't want to jump the gun with too many
functions.
