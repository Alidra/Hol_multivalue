require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1710164 : Prf (∀ (λ x : El real, (= (real_sgn x) ((@COND real) (real_lt (real_of_num (NUMERAL _0)) x) (real_of_num (NUMERAL (BIT1 _0))) ((@COND real) (real_lt x (real_of_num (NUMERAL _0))) (real_neg (real_of_num (NUMERAL (BIT1 _0)))) (real_of_num (NUMERAL _0)))))));
