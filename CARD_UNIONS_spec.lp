require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7062799 [A] : Prf (∀ (λ s : El (fun (fun A bool) bool), (⇒ (∧ ((@FINITE (fun A bool)) s) (∧ (∀ (λ t : El (fun A bool), (⇒ ((@IN (fun A bool)) t s) ((@FINITE A) t)))) (∀ (λ t : El (fun A bool), (∀ (λ u : El (fun A bool), (⇒ (∧ ((@IN (fun A bool)) t s) (∧ ((@IN (fun A bool)) u s) (¬ (= t u)))) (= ((@INTER A) t u) (@EMPTY A))))))))) (= ((@CARD A) ((@UNIONS A) s)) ((@nsum (fun A bool)) s (@CARD A))))));
