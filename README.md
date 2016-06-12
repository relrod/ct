# ct [![Build Status](https://travis-ci.org/relrod/ct.svg?branch=master)](https://travis-ci.org/relrod/ct)

An attempt at a category theory encoding in Coq, for learning purposes.

## Layout

Core concepts (`Category`, `Functor`, `NaturalTransformation`, `Monoid`, etc.)
are in the root of the project. Instances and derivations both live in the
`Instance` directory (and thus the `CT.Instance` namespace.

Thus if you wish to work with, for example, functor categories, you'll likely
want to do something like:

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

These are mostly made-up terms, but we have been using them pretty consistently
in our documentation/on IRC.

## References

... so far.

* https://arxiv.org/pdf/1505.06430v1.pdf (and https://github.com/amintimany/Categories)
* The [Homotopy Type Theory](https://github.com/HoTT/Hott) source
* [Basic Category Theory](http://www.cambridge.org/us/academic/subjects/mathematics/logic-categories-and-sets/basic-category-theory)
* [copumpkin/categories](https://github.com/copumpkin/categories/) - an Agda encoding of category theory

## License

MIT
