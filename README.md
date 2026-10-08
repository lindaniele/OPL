# OperatorPrecedenceLanguages
THIS WORK IS STILL IN PROGRESS

A Lean 4 / Mathlib formalization of operator precedence languages (OPL).

## Layout (as of now)

`OPL.lean` root module, imports the whole library
`OPL/Alphabet.lean`  Section I.1: OP alphabets, chains, depth, compatible words (Def. I.1.3–I.1.6)
`OPL/Determinization.lean` ...things on the paper
`OPL/Grammar.lean` 
`OPL/Automaton.lean`
`OPL/Logic.lean`
`OPL/Statements.lean`
`OPL/Examples.lean` contains the tests, inspired from the expression `n + n × Ln + nM`

Currently, there are 6 theorems and 21 "sorry"s

## Build

```sh
lake update        # fetch Mathlib and write lake-manifest.json
lake exe cache get # download the prebuilt Mathlib oleans (a few GB)
lake build
```

If `lake update` pulls a Mathlib revision built for a different Lean release,
align `lean-toolchain` with the one shipped by that revision.
