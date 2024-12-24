require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3210122 [A] : Prf (∀ (λ P : El (fun A bool), (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun A bool), (= (∀ (λ x : El A, (⇒ ((@IN A) x ((@UNION A) s t)) (P x)))) (∧ (∀ (λ x : El A, (⇒ ((@IN A) x s) (P x)))) (∀ (λ x : El A, (⇒ ((@IN A) x t) (P x))))))))))));
