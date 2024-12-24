require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1067805 [A B] : Prf (∀ (λ P : El (fun (Sum A B) bool), (⇒ (∧ (∀ (λ a : El A, (P ((@INL A B) a)))) (∀ (λ a : El B, (P ((@INR A B) a))))) (∀ (λ x : El (Sum A B), (P x))))));
