require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1482981 (P : El (fun real bool)) (x : El real) : Prf (= (P (real_abs x)) (∨ (∧ (real_ge x (real_of_num (NUMERAL _0))) (P x)) (∧ (real_gt (real_of_num (NUMERAL _0)) x) (P (real_neg x)))));
