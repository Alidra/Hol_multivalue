require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3384547 [A B] : Prf (∀ (λ f : El (fun A B), (∀ (λ s : El (fun A bool), (∀ (λ a : El A, (⇒ (∧ (∀ (λ x : El A, (∀ (λ y : El A, (⇒ (∧ ((@IN A) x s) (∧ ((@IN A) y s) (= (f x) (f y)))) (= x y)))))) ((@IN A) a s)) (= ((@IMAGE A B) f ((@DELETE A) s a)) ((@DELETE B) ((@IMAGE A B) f s) (f a))))))))));
