require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem18994 [A] (P : El (fun A bool)) (Q : El bool) : Prf ((λ Q' : El bool, (= (∨ (∃ (λ x : El A, (P x))) Q') (∃ (λ x : El A, (∨ (P x) Q'))))) Q);
