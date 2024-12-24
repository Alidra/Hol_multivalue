require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4289223 [A] : Prf (∀ (λ f : El (fun A A), (∀ (λ s : El (fun A bool), (⇒ (∧ ((@FINITE A) s) (∀ (λ x : El A, (⇒ ((@IN A) x s) (∧ ((@IN A) (f x) s) (∧ (¬ (= (f x) x)) (= (f (f x)) x))))))) (EVEN ((@CARD A) s)))))));
