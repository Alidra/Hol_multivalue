require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term4 (x0: El real) ≔ ((λ y0 : El real, (= (real_sgn y0) ((@COND real) (real_lt (real_of_num (NUMERAL _0)) y0) (real_of_num (NUMERAL (BIT1 _0))) ((@COND real) (real_lt y0 (real_of_num (NUMERAL _0))) (real_neg (real_of_num (NUMERAL (BIT1 _0)))) (real_of_num (NUMERAL _0)))))) x0);
symbol term2 (x0: El real) ≔ ((@COND real) (real_lt (real_of_num (NUMERAL _0)) x0) (real_of_num (NUMERAL (BIT1 _0))) ((@COND real) (real_lt x0 (real_of_num (NUMERAL _0))) (real_neg (real_of_num (NUMERAL (BIT1 _0)))) (real_of_num (NUMERAL _0))));
symbol term3 ≔ (∀ (λ y0 : El real, (= (real_sgn y0) ((@COND real) (real_lt (real_of_num (NUMERAL _0)) y0) (real_of_num (NUMERAL (BIT1 _0))) ((@COND real) (real_lt y0 (real_of_num (NUMERAL _0))) (real_neg (real_of_num (NUMERAL (BIT1 _0)))) (real_of_num (NUMERAL _0)))))));
symbol term0 ≔ (λ y0 : El real, ((@COND real) (real_lt (real_of_num (NUMERAL _0)) y0) (real_of_num (NUMERAL (BIT1 _0))) ((@COND real) (real_lt y0 (real_of_num (NUMERAL _0))) (real_neg (real_of_num (NUMERAL (BIT1 _0)))) (real_of_num (NUMERAL _0)))));
symbol term1 (x0: El real) ≔ ((λ y0 : El real, ((@COND real) (real_lt (real_of_num (NUMERAL _0)) y0) (real_of_num (NUMERAL (BIT1 _0))) ((@COND real) (real_lt y0 (real_of_num (NUMERAL _0))) (real_neg (real_of_num (NUMERAL (BIT1 _0)))) (real_of_num (NUMERAL _0))))) x0);
