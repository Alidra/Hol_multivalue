require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3624673 [A B C] : Prf (∀ (λ f : El (fun A B), (∀ (λ g : El (fun A C), (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun B bool), (⇒ (∧ ((@SUBSET B) ((@IMAGE A B) f s) t) (∧ ((@FINITE B) t) (∀ (λ x : El A, (∀ (λ y : El A, (⇒ (∧ ((@IN A) x s) (∧ ((@IN A) y s) (= (f x) (f y)))) (= (g x) (g y))))))))) ((@FINITE C) ((@IMAGE A C) g s)))))))))));
