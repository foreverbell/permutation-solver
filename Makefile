all:
	coqc PermutationSolver.v

clean:
	rm -f *.vo *.glob .*.aux
