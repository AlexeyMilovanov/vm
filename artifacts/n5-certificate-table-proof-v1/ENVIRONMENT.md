# Archived verification environment

The fresh archived run was executed under:

* WSL2 Linux `6.18.33.2-microsoft-standard-WSL2`, x86-64;
* Python `3.12.3`;
* GCC/cc `13.3.0` from Ubuntu 24.04;
* 16 logical processors available;
* six exact workers pinned to CPUs `4,6,8,10,12,14` at `nice 15`.

These versions describe the archived run; they are not mathematical
assumptions.  The portable checker requires only Python 3.10+ and a C compiler
with OpenMP support.

