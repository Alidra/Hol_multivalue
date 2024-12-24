require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3376778 [A B] : Prf (∀ (λ f : El (fun A B), (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun A bool), (⇒ (∀ (λ x : El A, (∀ (λ y : El A, (⇒ (∧ ((@IN A) x s) (∧ ((@IN A) y t) (= (f x) (f y)))) (= x y)))))) (= ((@IMAGE A B) f ((@DIFF A) s t)) ((@DIFF B) ((@IMAGE A B) f s) ((@IMAGE A B) f t))))))))));
