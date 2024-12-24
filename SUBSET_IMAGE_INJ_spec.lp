require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3641047 [A B] : Prf (∀ (λ f : El (fun A B), (∀ (λ s : El (fun B bool), (∀ (λ t : El (fun A bool), (= ((@SUBSET B) s ((@IMAGE A B) f t)) (∃ (λ u : El (fun A bool), (∧ ((@SUBSET A) u t) (∧ (∀ (λ x : El A, (∀ (λ y : El A, (⇒ (∧ ((@IN A) x u) ((@IN A) y u)) (= (= (f x) (f y)) (= x y))))))) (= s ((@IMAGE A B) f u)))))))))))));
