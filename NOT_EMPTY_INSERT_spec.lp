require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3279167 [A] : Prf (∀ (λ x : El A, (∀ (λ s : El (fun A bool), (¬ (= (@EMPTY A) ((@INSERT A) x s)))))));
