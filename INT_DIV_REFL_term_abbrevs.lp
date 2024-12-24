require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 ≔ (∀ (λ y0 : El int, (= (div y0 y0) ((@COND int) (= y0 (int_of_num (NUMERAL _0))) (int_of_num (NUMERAL _0)) (int_of_num (NUMERAL (BIT1 _0)))))));
