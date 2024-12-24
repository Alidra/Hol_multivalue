require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4810017 [A] : Prf (∀ (λ r : El (fun A (fun A bool)), (∀ (λ x : El A, (∀ (λ s : El (fun A bool), (⇒ (∀ (λ y : El A, (⇒ ((@IN A) y s) (= (r x y) (r y x))))) (= ((@pairwise A) r ((@INSERT A) x s)) (∧ (∀ (λ y : El A, (⇒ (∧ ((@IN A) y s) (¬ (= y x))) (r x y)))) ((@pairwise A) r s))))))))));
