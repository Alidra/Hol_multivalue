require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term3 ≔ (∀ (λ y0 : El nadd, (= (nadd_inv y0) ((@COND nadd) (nadd_eq y0 (nadd_of_num (NUMERAL _0))) (nadd_of_num (NUMERAL _0)) (mk_nadd (nadd_rinv y0))))));
symbol term0 ≔ (λ y0 : El nadd, ((@COND nadd) (nadd_eq y0 (nadd_of_num (NUMERAL _0))) (nadd_of_num (NUMERAL _0)) (mk_nadd (nadd_rinv y0))));
symbol term1 (x0: El nadd) ≔ ((λ y0 : El nadd, ((@COND nadd) (nadd_eq y0 (nadd_of_num (NUMERAL _0))) (nadd_of_num (NUMERAL _0)) (mk_nadd (nadd_rinv y0)))) x0);
symbol term2 (x0: El nadd) ≔ ((@COND nadd) (nadd_eq x0 (nadd_of_num (NUMERAL _0))) (nadd_of_num (NUMERAL _0)) (mk_nadd (nadd_rinv x0)));
symbol term4 (x0: El nadd) ≔ ((λ y0 : El nadd, (= (nadd_inv y0) ((@COND nadd) (nadd_eq y0 (nadd_of_num (NUMERAL _0))) (nadd_of_num (NUMERAL _0)) (mk_nadd (nadd_rinv y0))))) x0);
