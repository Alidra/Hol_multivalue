require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 ≔ (∀ (λ y0 : El int, (∀ (λ y1 : El int, (= (rem (int_neg y0) y1) ((@COND int) (= (rem y0 y1) (int_of_num (NUMERAL _0))) (int_of_num (NUMERAL _0)) (int_sub (int_abs y1) (rem y0 y1))))))));
