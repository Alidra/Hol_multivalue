require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3186538 [A] : Prf (∀ (λ s : El (fun A bool), (∀ (λ x : El A, (= ((@INSERT A) x s) (λ y : El A, (∨ ((@IN A) y s) (= y x))))))));
