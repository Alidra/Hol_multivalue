require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4356 [A] : Prf (∀ (λ P : El (fun A bool), (= ((@∃! A) (λ x : El A, (P x))) (∧ (∃ (λ x : El A, (P x))) (∀ (λ x : El A, (∀ (λ x' : El A, (⇒ (∧ (P x) (P x')) (= x x'))))))))));
