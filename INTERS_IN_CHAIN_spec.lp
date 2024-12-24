require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3781456 [A] : Prf (∀ (λ f : El (fun (fun A bool) bool), (⇒ (∧ ((@FINITE (fun A bool)) f) (∧ (¬ (= f (@EMPTY (fun A bool)))) (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun A bool), (⇒ (∧ ((@IN (fun A bool)) s f) ((@IN (fun A bool)) t f)) (∨ ((@SUBSET A) s t) ((@SUBSET A) t s))))))))) ((@IN (fun A bool)) ((@INTERS A) f) f))));
