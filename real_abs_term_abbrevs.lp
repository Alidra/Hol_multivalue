require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 ≔ (λ y0 : El real, ((@COND real) (real_le (real_of_num (NUMERAL _0)) y0) y0 (real_neg y0)));
symbol term1 (x0: El real) ≔ ((λ y0 : El real, ((@COND real) (real_le (real_of_num (NUMERAL _0)) y0) y0 (real_neg y0))) x0);
symbol term4 (x0: El real) ≔ ((λ y0 : El real, (= (real_abs y0) ((@COND real) (real_le (real_of_num (NUMERAL _0)) y0) y0 (real_neg y0)))) x0);
symbol term2 (x0: El real) ≔ ((@COND real) (real_le (real_of_num (NUMERAL _0)) x0) x0 (real_neg x0));
symbol term3 ≔ (∀ (λ y0 : El real, (= (real_abs y0) ((@COND real) (real_le (real_of_num (NUMERAL _0)) y0) y0 (real_neg y0)))));
