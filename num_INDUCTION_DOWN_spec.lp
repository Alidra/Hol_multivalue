require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem123857 : Prf (∀ (λ P : El (fun num bool), (∀ (λ m : El num, (⇒ (∧ (∀ (λ n : El num, (⇒ (<= m n) (P n)))) (∀ (λ n : El num, (⇒ (∧ (< n m) (P (+ n (NUMERAL (BIT1 _0))))) (P n))))) (∀ (λ n : El num, (P n))))))));
