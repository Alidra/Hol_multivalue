require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4524 [A] : Prf (∀ (λ P : El (fun A bool), (∀ (λ a : El A, (= (∃ (λ x : El A, (∧ (= a x) (P x)))) (P a))))));
