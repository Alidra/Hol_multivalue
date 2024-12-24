require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 ≔ (∧ (∀ (λ y0 : El num, (= (PRE (NUMERAL y0)) (NUMERAL (PRE y0))))) (∧ (= (PRE _0) _0) (∧ (∀ (λ y0 : El num, (= (PRE (BIT0 y0)) ((@COND num) (= y0 _0) _0 (BIT1 (PRE y0)))))) (∀ (λ y0 : El num, (= (PRE (BIT1 y0)) (BIT0 y0)))))));
