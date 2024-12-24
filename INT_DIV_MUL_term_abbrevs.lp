require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 ≔ (∧ (∀ (λ y0 : El int, (∀ (λ y1 : El int, (⇒ (¬ (= y1 (int_of_num (NUMERAL _0)))) (= (div (int_mul y0 y1) y1) y0)))))) (∀ (λ y0 : El int, (∀ (λ y1 : El int, (⇒ (¬ (= y0 (int_of_num (NUMERAL _0)))) (= (div (int_mul y0 y1) y0) y1)))))));
