require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3734144 [A B] : Prf (∀ (λ f : El (fun A B), (∀ (λ s : El (fun A bool), (= ((@FINITE B) ((@IMAGE A B) f s)) (∃ (λ t : El (fun A bool), (∧ ((@FINITE A) t) (∧ ((@SUBSET A) t s) (∧ (= ((@IMAGE A B) f s) ((@IMAGE A B) f t)) (∀ (λ x : El A, (∀ (λ y : El A, (⇒ (∧ ((@IN A) x t) ((@IN A) y t)) (= (= (f x) (f y)) (= x y)))))))))))))))));
