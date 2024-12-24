require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem16433 [A] (P : El bool) (Q : El (fun A bool)) : Prf ((λ Q' : El (fun A bool), (= (∃ (λ x : El A, (∧ P (Q' x)))) (∧ P (∃ (λ x : El A, (Q' x)))))) Q);
