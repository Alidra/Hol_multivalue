require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1581662 (z : El real) (x : El real) (y : El real) : Prf (∧ (= (real_min x y) (real_min y x)) (∧ (= (real_min (real_min x y) z) (real_min x (real_min y z))) (∧ (= (real_min x (real_min y z)) (real_min y (real_min x z))) (∧ (= (real_min x x) x) (= (real_min x (real_min x y)) (real_min x y))))));
