require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3382023 [A B] : Prf (∀ (λ f : El (fun A B), (∀ (λ s : El (fun A bool), (∀ (λ a : El A, (⇒ (∀ (λ x : El A, (⇒ (∧ ((@IN A) x s) (= (f x) (f a))) (= x a)))) (= ((@IMAGE A B) f ((@DELETE A) s a)) ((@DELETE B) ((@IMAGE A B) f s) (f a))))))))));
