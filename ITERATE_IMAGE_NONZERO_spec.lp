require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem6155069 [A B C] : Prf (∀ (λ op : El (fun C (fun C C)), (⇒ ((@monoidal C) op) (∀ (λ g : El (fun B C), (∀ (λ f : El (fun A B), (∀ (λ s : El (fun A bool), (⇒ (∧ ((@FINITE A) s) (∀ (λ x : El A, (∀ (λ y : El A, (⇒ (∧ ((@IN A) x s) (∧ ((@IN A) y s) (∧ (¬ (= x y)) (= (f x) (f y))))) (= (g (f x)) ((@neutral C) op)))))))) (= ((@iterate C B) op ((@IMAGE A B) f s) g) ((@iterate C A) op s ((@o A B C) g f)))))))))))));
