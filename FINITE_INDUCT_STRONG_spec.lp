require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3558722 [A] : Prf (∀ (λ P : El (fun (fun A bool) bool), (⇒ (∧ (P (@EMPTY A)) (∀ (λ x : El A, (∀ (λ s : El (fun A bool), (⇒ (∧ (P s) (∧ (¬ ((@IN A) x s)) ((@FINITE A) s))) (P ((@INSERT A) x s)))))))) (∀ (λ s : El (fun A bool), (⇒ ((@FINITE A) s) (P s)))))));
