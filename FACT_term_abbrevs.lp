require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 ≔ (∀ (λ y0 : El num, (= (FACT (SUC y0)) (* (SUC y0) (FACT y0)))));
symbol term3 ≔ (∧ (= (FACT (NUMERAL _0)) (NUMERAL (BIT1 _0))) (∀ (λ y0 : El num, (= (FACT (SUC y0)) (* (SUC y0) (FACT y0))))));
symbol term1 ≔ (FACT (NUMERAL _0));
symbol term2 ≔ (NUMERAL (BIT1 _0));
