require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3630638 [A B] : Prf (∀ (λ f : El (fun A B), (⇒ (∀ (λ x : El A, (∀ (λ y : El A, (⇒ (= (f x) (f y)) (= x y)))))) (∀ (λ s : El (fun A bool), (⇒ ((@INFINITE A) s) ((@INFINITE B) ((@IMAGE A B) f s))))))));
