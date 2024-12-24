require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2305588 (z : El int) (x : El int) (y : El int) : Prf (∧ (= (int_min x y) (int_min y x)) (∧ (= (int_min (int_min x y) z) (int_min x (int_min y z))) (∧ (= (int_min x (int_min y z)) (int_min y (int_min x z))) (∧ (= (int_min x x) x) (= (int_min x (int_min x y)) (int_min x y))))));
