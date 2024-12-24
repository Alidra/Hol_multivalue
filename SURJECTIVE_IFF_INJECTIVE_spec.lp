require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4945027 [A] : Prf (∀ (λ s : El (fun A bool), (∀ (λ f : El (fun A A), (⇒ (∧ ((@FINITE A) s) ((@SUBSET A) ((@IMAGE A A) f s) s)) (= (∀ (λ y : El A, (⇒ ((@IN A) y s) (∃ (λ x : El A, (∧ ((@IN A) x s) (= (f x) y))))))) (∀ (λ x : El A, (∀ (λ y : El A, (⇒ (∧ ((@IN A) x s) (∧ ((@IN A) y s) (= (f x) (f y)))) (= x y))))))))))));
