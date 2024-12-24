require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem17991 [A] (P : El (fun A bool)) : Prf (= (= (¬ (∀ (λ x : El A, (P x)))) (∃ (λ x : El A, (¬ (P x))))) (= (¬ (∀ P)) (∃ (λ x : El A, (¬ (P x))))));
