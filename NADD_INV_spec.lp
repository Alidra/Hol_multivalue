require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1308248 : Prf (∀ (λ x : El nadd, (= (dest_nadd (nadd_inv x)) ((@COND (fun num num)) (nadd_eq x (nadd_of_num (NUMERAL _0))) (λ n : El num, (NUMERAL _0)) (nadd_rinv x)))));
