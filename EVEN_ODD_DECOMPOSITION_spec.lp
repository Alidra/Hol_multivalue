require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem134538 : Prf (∀ (λ n : El num, (= (∃ (λ k : El num, (∃ (λ m : El num, (∧ (ODD m) (= n (* (EXP (NUMERAL (BIT0 (BIT1 _0))) k) m))))))) (¬ (= n (NUMERAL _0))))));
