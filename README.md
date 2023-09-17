# Shape-Analysis-Final-Project

To run examples, change the file address in example_file.

The analysis will report of any possible violations of: assertions in the program, null-pointers, multiple heap-shared nodes, cycles in the heap.

As a default, the program will print models of the sets of states at the output of the fixpoint algorithms - over-approximations 
of the sets of states reachable at every program location. The images will appear in the folder 'shape_figures'

Other options you might want to change:

Toggle on/off the parity analysis - this is done in the 'state' file

Change the set of abstraction predicates - this is done in the 'transformers' file in cannonical_embed_set
