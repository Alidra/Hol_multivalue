require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3252516 [A] (P : El (fun (fun A bool) bool)) : Prf (∀ (λ a : El A, (∀ (λ t : El (fun A bool), (= (∀ (λ s : El (fun A bool), (⇒ ((@SUBSET A) s ((@INSERT A) a t)) (P s)))) (∀ (λ s : El (fun A bool), (⇒ ((@SUBSET A) s t) (∧ (P s) (P ((@INSERT A) a s)))))))))));
