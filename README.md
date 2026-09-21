# OperatorPrecedenceLanguages

A Lean 4 / Mathlib formalization of operator precedence languages (OPL).

## Layout (as of now)

| File | Content |
| --- | --- |
| `OPL.lean` | root module, imports the whole library |
| `OPL/Alphabet.lean` | Section I.1: OP alphabets, chains, depth, compatible words (Def. I.1.3–I.1.6) |

## Build

```sh
lake update        # fetch Mathlib and write lake-manifest.json
lake exe cache get # download the prebuilt Mathlib oleans (a few GB)
lake build
```

If `lake update` pulls a Mathlib revision built for a different Lean release,
align `lean-toolchain` with the one shipped by that revision.
