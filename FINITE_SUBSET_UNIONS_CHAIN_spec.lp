require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3789348 [A] : Prf (∀ (λ f : El (fun (fun A bool) bool), (∀ (λ s : El (fun A bool), (⇒ (∧ ((@FINITE A) s) (∧ ((@SUBSET A) s ((@UNIONS A) f)) (∧ (¬ (= f (@EMPTY (fun A bool)))) (∀ (λ t : El (fun A bool), (∀ (λ u : El (fun A bool), (⇒ (∧ ((@IN (fun A bool)) t f) ((@IN (fun A bool)) u f)) (∨ ((@SUBSET A) t u) ((@SUBSET A) u t)))))))))) (∃ (λ t : El (fun A bool), (∧ ((@IN (fun A bool)) t f) ((@SUBSET A) s t)))))))));
