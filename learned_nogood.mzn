% learned_nogood.mzn
% 2-coloring a triangle (odd cycle): UNSAT, but typically not by immediate root contradiction.
% This usually forces at least one decision and then conflict analysis / learning.

var 1..2: a;
var 1..2: b;
var 1..2: c;

constraint a != b;
constraint b != c;
constraint c != a;

solve satisfy;

output [
  "a = ", show(a), "\n",
  "b = ", show(b), "\n",
  "c = ", show(c), "\n"
];