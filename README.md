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
