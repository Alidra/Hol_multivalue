require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1071853 [A] : Prf (∀ (λ P : El (fun (list A) bool), (⇒ (∧ (P (@NIL A)) (∀ (λ a0 : El A, (∀ (λ a1 : El (list A), (⇒ (P a1) (P ((@CONS A) a0 a1)))))))) (∀ (λ x : El (list A), (P x))))));
