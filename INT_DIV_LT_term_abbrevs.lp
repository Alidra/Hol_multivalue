require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 ≔ (∀ (λ y0 : El int, (∀ (λ y1 : El int, (⇒ (∧ (⇒ (¬ (= y1 (int_of_num (NUMERAL _0)))) (int_le (int_of_num (NUMERAL _0)) y0)) (int_lt y0 y1)) (= (div y0 y1) (int_of_num (NUMERAL _0))))))));
