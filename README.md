# theorem-prover

Repository holding code for first order logic theorem prover software. 

.axiom files are a custom declarative language whererin each definition is formed of statements. 

These roughly stem from an algebraic/relational form, however for syntactical sugar we allow extensions for this e.g. varargs for ALL statements. 

The software itself parses an axiom file ( and is also coded to allow for multiple axiom files to be imported safely ) 

A series of logical reductions and deductions are performed in addition to mathematical cloning and injection strategies ( e.g. cloning a statement and injecting an ELT into a ALL ). 

The logical reductions and deductions are relatively straightforward, although mostly employ recursive techniques, which we try to encapsulate as much as possible for clarity. 

The output of theorems is also relatively straightforward, although the reduction of variables is non-trivial, especially so with regards to 'preferred variables' which are coded in meta sections.
