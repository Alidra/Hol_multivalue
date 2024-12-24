require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1578322 (z : El real) (x : El real) (y : El real) : Prf (∧ (= (real_max x y) (real_max y x)) (∧ (= (real_max (real_max x y) z) (real_max x (real_max y z))) (∧ (= (real_max x (real_max y z)) (real_max y (real_max x z))) (∧ (= (real_max x x) x) (= (real_max x (real_max x y)) (real_max x y))))));
