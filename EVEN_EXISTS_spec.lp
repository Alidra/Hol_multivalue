require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem128828 : Prf (∀ (λ n : El num, (= (EVEN n) (∃ (λ m : El num, (= n (* (NUMERAL (BIT0 (BIT1 _0))) m)))))));
