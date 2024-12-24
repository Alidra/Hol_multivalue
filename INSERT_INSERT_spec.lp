require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3277193 [A] : Prf (∀ (λ x : El A, (∀ (λ s : El (fun A bool), (= ((@INSERT A) x ((@INSERT A) x s)) ((@INSERT A) x s))))));
