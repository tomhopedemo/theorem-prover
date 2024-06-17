Repository holding code for first order logic theorem prover software. 

.axiom files are a custom declarative language whererin each definition is formed of statements. 

These roughly stem from an algebraic/relational form, however for syntactical sugar we allow extensions for this e.g. varargs for ALL statements. 

The software itself parses an axiom file ( and is also coded to allow for multiple axiom files to be imported safely ) 

A series of logical reductions and deductions are performed in addition to mathematical cloning and injection strategies ( e.g. cloning a statement and injecting an ELT into a ALL ). 

The logical reductions and deductions are relatively straightforward, although mostly employ recursive techniques, which we try to encapsulate as much as possible for clarity. 

The output of theorems is also relatively straightforward, although the reduction of variables is non-trivial, especially so with regards to 'preferred variables' which are coded in meta sections.

Within the software there are two aspects which are tough problems whose solutions are only implemented to a modest degree.  

These are:

1. The identification of complex strategies which have a high chance of yielding reductionary results.  

2. The identification of 'interesting/important' results from the field of all results.

The first such problem is better attacked using a grid/parallel computing setup, and would likely further benefit by some form of ML involvement. 

The second issue appears to be more nuanced, since there are a couple of angles to look at. The first is how to exclude theorems which are both trivial and complex. (Note trivial deductions on their own are often interesting, ie corollary-like theorems)

The other side of this is how to identify the most interesting complex theorems from the results.
  
