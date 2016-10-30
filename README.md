# purescript-type-data

This experiment attempts to model data types at the type level and provide tools for computing with said definitions.  Including type variance checking and determining whether or not a data type could have a functor instance.

Check at the bottom of /src/Main.purs for an example with `Maybe`

Currently not very expressive: it can't talk about data types which refer to existing types - but it will do soon.

