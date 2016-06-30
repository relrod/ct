# ct [![Build Status](https://travis-ci.org/relrod/ct.svg?branch=master)](https://travis-ci.org/relrod/ct)

An attempt at a category theory encoding in Coq, for learning purposes.

## Layout

Core concepts (`Category`, `Functor`, `NaturalTransformation`, etc.)
are in the `CT` directory. Instances and derivations both live in the
`CT/Instance` directory (and thus the `CT.Instance` namespace). A simple
algebra hierarchy is found in `CT/Algebra`. Definitions there are largely
[decategorified](https://en.wikipedia.org/wiki/Categorification), even when the
structures can be defined purely categorically. There are instances (e.g.
`CT.Instance.Category.MonoidCategory` (the category for any given `Monoid`)
which make use of them.

The layout of the project is fairly simple. If you wish to work with, for
example, functor categories, you'll likely want to do something like:

```coq
Require Import CT.Category.
Require Import CT.Instance.Category.FunctorCategory.
(* ... *)
```

In any documentation we write, an **instance** is a particular usage of a
concept. For example `CT.Instance.Coq.Functor` exports a `CoqOptionFunctor`
which, as the name suggests, is a `Functor` for Coq's `option` type
(specifically it is an endofunctor from `CoqType -> CoqType`, where `CoqType`
is defined in `CT.Instance.Coq.Category` to be the category of Coq types).

We call something a **derivation** if passing it something generates a
specialized version of that thing. For example, `FunctorCategory` is a
derivation because it takes two `Category` parameters to return the functor
category between them. Similarly, a `MonoidCategory` takes a `Monoid` and
returns a `Category` with a single object (with composition defined by
`Monoid`'s `mu`).

These ("instance", "derivation") are mostly made-up terms, but we have been
using them pretty consistently in our documentation/on IRC.

## Notes on notation

We rarely use `Notation` or `Infix` in the library. This is intentional and done
for added clarity. While Coq's notation system can be extremely helpful
(especially in combination with `scope`s), since this is a library written
for educational purposes, we wish to not cloud any view of what is actually
happening. We do sprinkle in use of implicit arguments fairly liberally,
however.

## References

... so far.

* https://arxiv.org/pdf/1505.06430v1.pdf (and https://github.com/amintimany/Categories)
* The [Homotopy Type Theory](https://github.com/HoTT/HoTT) source
* [Basic Category Theory](http://www.cambridge.org/us/academic/subjects/mathematics/logic-categories-and-sets/basic-category-theory)
* [copumpkin/categories](https://github.com/copumpkin/categories/) - an Agda encoding of category theory

## License

MIT
