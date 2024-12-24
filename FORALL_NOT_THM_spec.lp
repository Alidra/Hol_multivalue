require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem10905 [A] : Prf (∀ (λ P : El (fun A bool), (= (∀ (λ x : El A, (¬ (P x)))) (¬ (∃ (λ x : El A, (P x)))))));
