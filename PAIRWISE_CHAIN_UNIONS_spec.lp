require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4825471 [A] : Prf (∀ (λ R : El (fun A (fun A bool)), (∀ (λ c : El (fun (fun A bool) bool), (⇒ (∧ (∀ (λ s : El (fun A bool), (⇒ ((@IN (fun A bool)) s c) ((@pairwise A) R s)))) (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun A bool), (⇒ (∧ ((@IN (fun A bool)) s c) ((@IN (fun A bool)) t c)) (∨ ((@SUBSET A) s t) ((@SUBSET A) t s)))))))) ((@pairwise A) R ((@UNIONS A) c)))))));
