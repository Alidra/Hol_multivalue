require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3278336 [A] : Prf (∀ (λ x : El A, (∀ (λ y : El A, (∀ (λ s : El (fun A bool), (= ((@INSERT A) x ((@INSERT A) y s)) ((@INSERT A) y ((@INSERT A) x s)))))))));
