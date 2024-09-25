# Normalising untyped lambda-terms, in a multitude of ways

This is an implementation of a number of algorithms to reduce lambda-terms to their normal forms!
It is intended to contain a "classic" syntactic substitution-based approach, as well as a number of NbE-based methods.
The NbE methods are inspired heavily by András Kovács's implementations in [elaboration-zoo](https://github.com/AndrasKovacs/elaboration-zoo/),
with me going through the pain of adapting them to Rust.

Currently, the following algorithms are implemented:

1. `rewrite` -- syntactic normalisation algorithm that performs reductions on terms one at a time,
until the normal form is reached.
2. `hoas-names` -- normalisation-by-evaluation algorithm based on representing values using
[higher-order abstract syntax](https://en.wikipedia.org/wiki/Higher-order_abstract_syntax). For binders,
plain names are used to reference values in environment, hence the name.
3. `closures-names` -- normalisation-by-evaluation algorithm based on representing values using closures.
They are not the closures of the host language, but rather function body as a term and an environment
packed together.
Plain names are used by binders.
