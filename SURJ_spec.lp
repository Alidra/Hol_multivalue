require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3201623 [A B] : Prf (∀ (λ t : El (fun B bool), (∀ (λ s : El (fun A bool), (∀ (λ f : El (fun A B), (= ((@SURJ A B) f s t) (∧ (∀ (λ x : El A, (⇒ ((@IN A) x s) ((@IN B) (f x) t)))) (∀ (λ x : El B, (⇒ ((@IN B) x t) (∃ (λ y : El A, (∧ ((@IN A) y s) (= (f y) x)))))))))))))));
