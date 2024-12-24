require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3052391 : Prf (∀ (λ P : El (fun num bool), (∀ (λ m : El num, (⇒ (∧ (∀ (λ n : El num, (⇒ (<= m n) (P n)))) (∀ (λ n : El num, (⇒ (∧ (< n m) (∀ (λ p : El num, (⇒ (< n p) (P p))))) (P n))))) (∀ (λ n : El num, (P n))))))));
