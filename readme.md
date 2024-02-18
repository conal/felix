<div style="float:right; padding:10pt"><img width="200" src="Felix-the-Cat.png"/></div>

## Felix: an Agda category theory for denotational design

## Introduction

This library replaces the overgrown [denotational-hardware](https://github.com/conal/denotational-hardware) library, which had mixed general category theory with some functionality for hardware design.

## Dependencies

*   [Agda compiler](https://agda.readthedocs.io/en/latest/getting-started/installation.html#installing-the-agda-and-the-agda-mode-programs).
    Works with Agda 2.6.4.
*   The [Agda standard library (agda-stdlib)](https://github.com/agda/agda-stdlib).
    Works with agda-stdlib 2.0.
*   Haskell [ieee754 package](https://github.com/agda/agda/issues/3619) (as described under Troubleshooting below).

## Troubleshooting

You might see an error message like this:

```
Calling: ghc -O -o /Users/sseefried/code/agda-machines/Test -Werror -i/Users/sseefried/code/agda-machines -main-is MAlonzo.Code.Test /Users/sseefried/code/agda-machines/MAlonzo/Code/Test.hs --make -fwarn-incomplete-patterns -fno-warn-overlapping-patterns
[  1 of 153] Compiling MAlonzo.RTE      ( MAlonzo/RTE.hs, MAlonzo/RTE.o )
Compilation error:

MAlonzo/RTE.hs:9:1: error:
    Could not find module ‘Numeric.IEEE’
    Use -v (or `:set -v` in ghci) to see a list of the files searched for.
  |
9 | import Numeric.IEEE ( IEEE(identicalIEEE, nan) )
  | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
```

You can fix this error with:

```
cabal install --lib ieee754
```

You can find out how to more about this issue [here](https://github.com/agda/agda/issues/3619#issuecomment-665232148) and
[here](https://agda.readthedocs.io/en/latest/getting-started/installation.html#installing-the-agda-and-the-agda-mode-programs).
