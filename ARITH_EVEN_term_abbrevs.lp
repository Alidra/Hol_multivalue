require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 ≔ (∧ (∀ (λ y0 : El num, (= (EVEN (NUMERAL y0)) (EVEN y0)))) (∧ (= (EVEN _0) T) (∧ (∀ (λ y0 : El num, (= (EVEN (BIT0 y0)) T))) (∀ (λ y0 : El num, (= (EVEN (BIT1 y0)) F))))));
