require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4842239 [A] : Prf (∀ (λ P : El (fun (fun (fun A bool) bool) bool), (∀ (λ Q : El (fun (fun A bool) bool), (= ((@INTERSECTION_OF A) P Q) (λ s : El (fun A bool), (∃ (λ u : El (fun (fun A bool) bool), (∧ (P u) (∧ (∀ (λ c : El (fun A bool), (⇒ ((@IN (fun A bool)) c u) (Q c)))) (= ((@INTERS A) u) s)))))))))));
