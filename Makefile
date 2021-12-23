all:
	coqc PermutationSolver.v
	coqc Examples.v

clean:
	rm -f *.vo *.vok *.vos *.glob .*.aux

