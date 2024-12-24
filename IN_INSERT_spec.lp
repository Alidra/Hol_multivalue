require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3205665 [A] : Prf (∀ (λ x : El A, (∀ (λ y : El A, (∀ (λ s : El (fun A bool), (= ((@IN A) x ((@INSERT A) y s)) (∨ (= x y) ((@IN A) x s)))))))));
