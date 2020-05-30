# Prerequisites
1. `python3` must be installed in the system which can be installed with `sudo apt install python3`
2. `jupyter` python library is required

# How to run the notebook
1. Navigate using `cd 160101048/`
2. Run `jupyter notebook` terminal
3. A browser should open up with a tab that lists the contents of the folder
4. Select `solver.ipynb` to open the notebook

# How to run the code
1. The last cell in the notebook has been made to run the solver
2. Specify the input file eg. `input_file = "input/sat/bmc-2.cnf"`
3. Run this cell or alternatively all the cells

# Alternative to run
1. A script containing the same solver `solver.py` is present
2. Go to the end of the file and change the `input_file` variable as required.
3. Run `python3 solver.py`

# Sample output
```
SATISFIABLE
AC, All clauses evaluate to true under given assignment
## Statistics: 
# Restarts:  0
# Learned cluases:  50
# Decisions:  243
# Implications:  11615
# Time (s):  0.48908218200000064
```
# Input folder
Two folders from edusat `sat/` and `edusat/` containg input cnf files are present in `input`.

# Output folder
`output/` folder contains the verbose results obtained from previously tested, eg. `sat/bmc-1.out` for `input/sat/bmc-1.cnf` 

# Benchmarks
| Input name | time | Remarks | commit |
| --------------- | ---- | ---- | --- |
| unsat/bj08amba2g4f3.k9.cnf | real 4m14.763s, user 4m8.160s, sys 0m1.308s | | |
| sat/bmc-1.cnf | real 2m1.617s, user 1m55.716s, sys 0m1.292s |  |  |
| sat/bmc-2.cnf | real 0m1.690s, user 0m1.197s, sys 0m0.100s |  |  |
| sat/bmc-3.cnf | real 2m7.709s, user 2m2.657s, sys 0m1.160s |  |  |
| sat/bmc-4.cnf | real 2m51.223s, user 2m44.077s, sys 0m1.192s |  |  |
| sat/bmc-5.cnf | real 0m9.515s, user 0m7.982s, sys 0m0.248s |  |  |
| sat/bmc-6.cnf |  real 15m4.201s, user 14m41.354s, sys 0m6.085s|  |  |
| sat/bmc-7.cnf | real 0m6.610s user 0m3.418s, sys 0m0.226s |  |  |
| sat/bmc-8.cnf | real 9m21.227s, user 9m20.230s, sys 0m0.344s | | |
| sat/bmc-9.cnf | real 13m19.910s, user 13m17.934s, sys 0m0.892s | | |
| sat/bmc-10.cnf | real 29m28.093s, user 29m25.185s, sys 0m0.720s | | |
| sat/bmc-11.cnf | real 15m38.060s, user 15m36.147s, sys 0m0.420s | | |
| sat/bmc-13.cnf | real 1m48.175s, user 1m47.867s, sys 0m0.132s| | |
| sat/bmc-12.cnf | 2090.070481846s | | |