require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2968656 : Prf (∀ (λ P : El (fun num bool), (⇒ (∧ (P (NUMERAL _0)) (∀ (λ n : El num, (⇒ (P n) (∧ (P (* (NUMERAL (BIT0 (BIT1 _0))) n)) (P (+ (* (NUMERAL (BIT0 (BIT1 _0))) n) (NUMERAL (BIT1 _0))))))))) (∀ (λ n : El num, (P n))))));
