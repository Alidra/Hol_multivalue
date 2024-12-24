require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5037682 [A B] : Prf (∀ (λ f : El (fun A B), (= (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun A bool), (⇒ (= ((@IMAGE A B) f s) ((@IMAGE A B) f t)) (= s t)))))) (∀ (λ x : El A, (∀ (λ y : El A, (⇒ (= (f x) (f y)) (= x y)))))))));
