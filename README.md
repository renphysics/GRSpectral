# GRSpectral
A Mathematica package for solving PDEs by the pseudospectral method (v0.2, Jie Ren). It focuses on applications to General Relativity (GR) and is suitable for general boundary value problems, including eigenvalue problems.

Philosophy of the design: Leave complexity to ourselves, and give simplicity to users.

To be updated. (2025/05/19: Package name changed from `spNDSolve` to `GRSpectral`. v0.3 to be released.)

Put the `GRSpectral.m` in the directory

```mathematica
SystemOpen@FileNameJoin[{$UserBaseDirectory, "Applications"}]
```

Load the package by

```mathematica
<< GRSpectral.m
```

The documentation is in the notebook `GRSpectral Manual.nb` (to be completed).

1. At the first (symbolic) stage, specify equations and boundary conditions by `eqProcess`. 
2. At the second (numerical) stage, solve the system numerically by `spNDSolve`.

The folder PDW contains a nontrivial example as the background solution in 1612.04385 and 1705.05390.



# Functionalities of `GRSpectral`
## 1. Natural input of equations and boundary conditions
```mathematica
flist = {psi[z], phi[z]};
eqlist = {(-z + z^4 + phi[z]^2) psi[z] + (-1 + z^3) (3 z^2 Derivative[1][psi][z] + (-1 + z^3) Derivative[2][psi][z]), 2 phi[z] psi[z]^2 + (-1 + z^3) Derivative[2][phi][z]}; (*Equations of motion*)
bdylist1 = {psi'[z], phi[z] - mu}; (*Boundary conditions at z=0*)
bdylist2 = {3 z^2 psi'[z] - 2 psi[z], phi[z]}; (*Boundary conditions at z=1*)
eqProcess[flist, eqlist, {{z == 0, bdylist1}, {z == 1, bdylist2}}]; (*Impose boundary conditions*)
```
## 2. Grid construction
## 3. Method of continuation
## 4. Arbitrary precision
## 5. Eigenvalue problems
