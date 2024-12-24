require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem18916 [A] (P : El (fun A bool)) (Q : El (fun A bool)) : Prf ((λ Q' : El (fun A bool), (= (∨ (∃ (λ x : El A, (P x))) (∃ (λ x : El A, (Q' x)))) (∃ (λ x : El A, (∨ (P x) (Q' x)))))) Q);
