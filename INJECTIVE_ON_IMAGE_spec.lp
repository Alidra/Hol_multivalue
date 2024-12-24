require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5037470 [A B] : Prf (∀ (λ f : El (fun A B), (∀ (λ u : El (fun A bool), (= (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun A bool), (⇒ (∧ ((@SUBSET A) s u) (∧ ((@SUBSET A) t u) (= ((@IMAGE A B) f s) ((@IMAGE A B) f t)))) (= s t)))))) (∀ (λ x : El A, (∀ (λ y : El A, (⇒ (∧ ((@IN A) x u) (∧ ((@IN A) y u) (= (f x) (f y)))) (= x y)))))))))));
