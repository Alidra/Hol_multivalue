require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 ≔ (∧ (∀ (λ y0 : El num, (= (ODD (NUMERAL y0)) (ODD y0)))) (∧ (= (ODD _0) F) (∧ (∀ (λ y0 : El num, (= (ODD (BIT0 y0)) F))) (∀ (λ y0 : El num, (= (ODD (BIT1 y0)) T))))));
