# spNDSolve (Spectral NDSolve)
A Mathematica package for solving PDEs by the pseudospectral method (v0.2, Jie Ren)

Philosophy of the design: Leave complexity to ourselves, and give simplicity to users.

To be updated.

Put the `spNDSolve.m` in the directory

```
SystemOpen@FileNameJoin[{$UserBaseDirectory, "Applications"}]
```

Load the package by

```
<< spNDSolve.m
```

The documentation is in the notebook `spNDSolve Manual.nb` (to be completed).

1. At the first (symbolic) stage, specify equations and boundary conditions by `eqProcess`. 
2. At the second (numerical) stage, solve the system numerically by `spNDSolve`.

The folder PDW contains a nontrivial example as the background solution in 1612.04385 and 1705.05390.
