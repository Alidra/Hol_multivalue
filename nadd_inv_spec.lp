require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1308008 : Prf (∀ (λ x : El nadd, (= (nadd_inv x) ((@COND nadd) (nadd_eq x (nadd_of_num (NUMERAL _0))) (nadd_of_num (NUMERAL _0)) (mk_nadd (nadd_rinv x))))));
