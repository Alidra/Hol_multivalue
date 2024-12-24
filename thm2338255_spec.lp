require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2338255 [A] (P : El (fun A bool)) : Prf ((λ P' : El (fun A bool), (= (¬ (∀ (λ x : El A, (P' x)))) (∃ (λ x : El A, (¬ (P' x)))))) P);
