require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem21384 [A] (x : El A) (y : El A) (z : El A) : Prf (∧ (= x x) (∨ (¬ (= x y)) (∨ (¬ (= x z)) (= y z))));
