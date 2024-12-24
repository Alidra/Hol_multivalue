require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem18392 [A] (P : El (fun A bool)) : Prf (= (¬ (∀ P)) (∃ (λ x : El A, (¬ (P x)))));
