require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2305242 (z : El int) (x : El int) (y : El int) : Prf (∧ (= (int_max x y) (int_max y x)) (∧ (= (int_max (int_max x y) z) (int_max x (int_max y z))) (∧ (= (int_max x (int_max y z)) (int_max y (int_max x z))) (∧ (= (int_max x x) x) (= (int_max x (int_max x y)) (int_max x y))))));
