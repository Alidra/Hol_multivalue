require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 ≔ (∀ (λ y0 : El num, (∀ (λ y1 : El num, (∀ (λ y2 : El num, (∀ (λ y3 : El num, (∀ (λ y4 : El num, (⇒ (¬ (= y0 (NUMERAL _0))) (⇒ (∧ (= y1 y2) (¬ (= y3 y4))) (¬ (= (+ y1 (* y0 y3)) (+ y2 (* y0 y4))))))))))))))));
