require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term1 ≔ (λ y0 : El num, (= (* (NUMERAL (BIT0 (BIT1 _0))) y0) (+ y0 y0)));
symbol term0 (x0: El num) ≔ (* (NUMERAL (BIT0 (BIT1 _0))) x0);
symbol term3 ≔ (∀ (λ y0 : El num, (= (* (NUMERAL (BIT0 (BIT1 _0))) y0) (+ y0 y0))));
symbol term4 ≔ (∀ (λ y0 : El num, (= (+ y0 y0) (* (NUMERAL (BIT0 (BIT1 _0))) y0))));
symbol term2 ≔ (λ y0 : El num, (= (+ y0 y0) (* (NUMERAL (BIT0 (BIT1 _0))) y0)));
