require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term2 ≔ (∧ (∀ (λ y0 : El num, (= (+ (NUMERAL _0) y0) y0))) (∀ (λ y0 : El num, (∀ (λ y1 : El num, (= (+ (SUC y0) y1) (SUC (+ y0 y1))))))));
symbol term0 ≔ (∀ (λ y0 : El num, (∀ (λ y1 : El num, (= (+ (SUC y0) y1) (SUC (+ y0 y1)))))));
symbol term1 ≔ (∀ (λ y0 : El num, (= (+ (NUMERAL _0) y0) y0)));
