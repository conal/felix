## Felix: an Agda category theory for denotational design

## Introduction

[This library replaces the overgrown denotational-hardware library, which had mixed general category theory with some functionality for hardware design.]

## Dependencies

*   [Agda compiler](https://agda.readthedocs.io/en/latest/getting-started/installation.html#installing-the-agda-and-the-agda-mode-programs).
    Known to work with Agda 2.6.2
*   The [Agda standard library (agda-stdlib)](https://github.com/agda/agda-stdlib).
    Known to work with version 1.7.
*   Haskell [ieee754 package](https://github.com/agda/agda/issues/3619) (as described under Troubleshooting below)

## Building

Makefile targets:

*   `compile`: compiles the `Test` module, but you can compile faster from within the Emacs mode (`∁-c C­x C-c`).
*   `tests`: generates circuit diagrams in the `Figures` subdirectory (dot files and their PDF renderings).
*   `listings`: renders source code to deeply hyper-linked HTML.
    Start perusing at `html/Everything.html`.

## Summary of important modules

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
