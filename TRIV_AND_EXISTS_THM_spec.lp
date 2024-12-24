require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem6010 [A] : Prf (∀ (λ P : El bool, (∀ (λ Q : El bool, (= (∧ (∃ (λ x : El A, P)) (∃ (λ x : El A, Q))) (∃ (λ x : El A, (∧ P Q))))))));
