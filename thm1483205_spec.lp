require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1483205 (y : El real) (P : El (fun real bool)) (x : El real) : Prf (= (P (real_max x y)) (∨ (∧ (real_ge y x) (P y)) (∧ (real_gt x y) (P x))));
