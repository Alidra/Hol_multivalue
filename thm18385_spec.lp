require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem18385 [A] (P : El (fun A bool)) : Prf (= (¬ ((@∃! A) (λ x : El A, (P x)))) (∨ (∀ (λ x : El A, (¬ (P x)))) (∃ (λ x : El A, (∃ (λ y : El A, (∧ (P x) (∧ (P y) (¬ (= y x))))))))));
