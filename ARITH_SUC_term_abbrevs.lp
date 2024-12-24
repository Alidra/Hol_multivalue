require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 ≔ (∧ (∀ (λ y0 : El num, (= (SUC (NUMERAL y0)) (NUMERAL (SUC y0))))) (∧ (= (SUC _0) (BIT1 _0)) (∧ (∀ (λ y0 : El num, (= (SUC (BIT0 y0)) (BIT1 y0)))) (∀ (λ y0 : El num, (= (SUC (BIT1 y0)) (BIT0 (SUC y0))))))));
