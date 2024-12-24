require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 ≔ (∀ (λ y0 : El int, (∀ (λ y1 : El int, (∀ (λ y2 : El int, (∀ (λ y3 : El int, (∀ (λ y4 : El int, (⇒ (¬ (= y0 (int_of_num (NUMERAL _0)))) (⇒ (∧ (= y1 y2) (¬ (= y3 y4))) (¬ (= (int_add y1 (int_mul y0 y3)) (int_add y2 (int_mul y0 y4))))))))))))))));
