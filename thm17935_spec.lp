require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem17935 [A] (y : El A) (x : El A) : Prf (= ((λ y' : El A, (= (= x y') (= y' x))) y) (= (= x y) (= y x)));
