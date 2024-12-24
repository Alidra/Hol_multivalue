require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4004559 [A B] : Prf (∀ (λ f : El (fun A B), (∀ (λ s : El (fun A bool), (∀ (λ n : El num, (⇒ (∧ (∀ (λ x : El A, (∀ (λ y : El A, (⇒ (∧ ((@IN A) x s) (∧ ((@IN A) y s) (= (f x) (f y)))) (= x y)))))) ((@HAS_SIZE A) s n)) ((@HAS_SIZE B) ((@IMAGE A B) f s) n))))))));
