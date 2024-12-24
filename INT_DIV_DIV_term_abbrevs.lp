require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 ≔ (∀ (λ y0 : El int, (∀ (λ y1 : El int, (∀ (λ y2 : El int, (⇒ (int_le (int_of_num (NUMERAL _0)) y1) (= (div (div y0 y1) y2) (div y0 (int_mul y1 y2))))))))));
