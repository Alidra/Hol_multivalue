require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5950 [A] : Prf (∀ (λ P : El bool, (∀ (λ Q : El (fun A bool), (= (∧ P (∃ (λ x : El A, (Q x)))) (∃ (λ x : El A, (∧ P (Q x)))))))));
