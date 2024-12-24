require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2976208 : Prf (∀ (λ P : El (fun num bool), (= (∀ (λ n : El num, (P n))) (∧ (∀ (λ n : El num, (P (* (NUMERAL (BIT0 (BIT1 _0))) n)))) (∀ (λ n : El num, (P (+ (* (NUMERAL (BIT0 (BIT1 _0))) n) (NUMERAL (BIT1 _0))))))))));
