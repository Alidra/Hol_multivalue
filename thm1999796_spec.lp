require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1999796 (x : El real) (y : El real) : Prf (= (= (real_lt x y) (∧ (real_lt x y) (¬ (= x y)))) (= (real_lt x y) (∧ (real_lt x y) (¬ (= x y)))));
