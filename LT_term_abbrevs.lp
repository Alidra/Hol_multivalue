require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term1 ≔ (∀ (λ y0 : El num, (= (< y0 (NUMERAL _0)) F)));
symbol term2 ≔ (∧ (∀ (λ y0 : El num, (= (< y0 (NUMERAL _0)) F))) (∀ (λ y0 : El num, (∀ (λ y1 : El num, (= (< y0 (SUC y1)) (∨ (= y0 y1) (< y0 y1))))))));
symbol term0 ≔ (∀ (λ y0 : El num, (∀ (λ y1 : El num, (= (< y0 (SUC y1)) (∨ (= y0 y1) (< y0 y1)))))));
