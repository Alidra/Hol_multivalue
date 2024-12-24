require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3450827 [A] : Prf (∀ (λ P : El (fun (fun A bool) bool), (⇒ (∧ (P (@EMPTY A)) (∀ (λ a : El A, (∀ (λ s : El (fun A bool), (⇒ (¬ ((@IN A) a s)) (P ((@INSERT A) a s)))))))) (∀ (λ s : El (fun A bool), (P s))))));
