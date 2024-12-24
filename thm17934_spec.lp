require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem17934 [A] (x : El A) (y : El A) : Prf ((λ y' : El A, (= (= x y') (= y' x))) y);
