Strongly-typed bound
===

[Bound](http://hackage.haskell.org/package/bound) is a library for manipulating terms containing variables. Terms written using the library are guaranteed to be well-scoped. I was quite happy to [stumble](http://gelisam.blogspot.ca/2014/10/understanding-strongly-typed-bound-part.html) upon a snippet describing a strongly-typed version, meaning that the terms are also guaranteed to be well-typed.

[Edward Kmett's original 2012 snippet](http://lpaste.net/79582) has it all: type families, data kinds, higher-ranked monad transformers, tasteful uses of `unsafePerformIO` and `unsafeCoerce`, and even a gratuitious use of comonads. At only 255 lines of code, it's a compact way to demonstrate the purpose of those more advanced Haskell features, but it can also be a bit daunting to read.

To make the ideas of strongly-typed bound easier to digest, I have written a version which is less general, uses fewer tricks, and has more comments.

Motivation
---

If I was asked to represent the simply-typed lambda calculus, my first attempt would probably look like this.

```haskell
data Exp a where
    Unit :: Exp ()
    App :: Exp (a -> b) -> Exp a -> Exp b
    Lam :: (Exp a -> Exp b) -> Exp (a -> b)
```

The use of [HOAS](http://en.wikipedia.org/wiki/Higher-order_abstract_syntax) combined with phantom types guarantees that the terms will be well-scoped and well-typed. Unfortunately, in this representation the variables are implicit, which makes some manipulations (for example [Let-floating](http://research.microsoft.com/~simonpj/papers/float.ps.gz)) harder than they need to be.

To perform those kinds of manipulations, it is more convenient to represent variables via a concrete type such as integers or De Bruijn indices. In the following representation, `g` has _n_ inhabitants when _n_ variables are supposed to be in scope. For example, in the body of a lambda, the type `Maybe g` has one more inhabitant than `g` does, so we can refer to the variable bound by the lambda using `Var Nothing`. Inside of a nested lambda, `Var Nothing` now refers to the variable bound by the nested lambda, while the variable bound by the outer lambda is now named `Var (Just Nothing)`.

```haskell
data Exp g where
    Var :: g -> Exp g
    Unit :: Exp g
    App :: Exp g -> Exp g -> Exp g
    Lam :: Exp (Maybe g) -> Exp g
```

This representation ensures that our terms are well-scoped, but we have lost the guarantee that terms are well-typed. [StronglyTypedBound.hs](StronglyTypedBound.hs) demonstrates how this representation can be extended to get the best of both worlds: a concrete representation for variables, and terms which are both well-scoped and well-typed.
