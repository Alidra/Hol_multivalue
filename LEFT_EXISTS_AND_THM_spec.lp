require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5682 [A] : Prf (∀ (λ P : El (fun A bool), (∀ (λ Q : El bool, (= (∃ (λ x : El A, (∧ (P x) Q))) (∧ (∃ (λ x : El A, (P x))) Q))))));
