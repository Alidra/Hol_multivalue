require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1483429 (x : El real) (P : El (fun real bool)) (y : El real) : Prf (= (P (real_min x y)) (∨ (∧ (real_ge y x) (P x)) (∧ (real_gt x y) (P y))));
