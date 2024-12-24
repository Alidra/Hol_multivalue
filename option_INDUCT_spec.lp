require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1070232 [A] : Prf (∀ (λ P : El (fun (option A) bool), (⇒ (∧ (P (@NONE A)) (∀ (λ a : El A, (P ((@SOME A) a))))) (∀ (λ x : El (option A), (P x))))));
