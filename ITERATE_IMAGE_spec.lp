require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5942955 [A B C] : Prf (∀ (λ op : El (fun C (fun C C)), (⇒ ((@monoidal C) op) (∀ (λ f : El (fun A B), (∀ (λ g : El (fun B C), (∀ (λ s : El (fun A bool), (⇒ (∀ (λ x : El A, (∀ (λ y : El A, (⇒ (∧ ((@IN A) x s) (∧ ((@IN A) y s) (= (f x) (f y)))) (= x y)))))) (= ((@iterate C B) op ((@IMAGE A B) f s) g) ((@iterate C A) op s ((@o A B C) g f)))))))))))));
