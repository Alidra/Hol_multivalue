require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem309905 [A] (<< : El (fun A (fun A bool))) : Prf (= (∀ (λ P : El (fun A bool), (⇒ (∃ (λ x : El A, (P x))) (∃ (λ x : El A, (∧ (P x) (∀ (λ y : El A, (⇒ (<< y x) (¬ (P y))))))))))) (∀ (λ P : El (fun A bool), (⇒ (∀ (λ x : El A, (⇒ (∀ (λ y : El A, (⇒ (<< y x) (P y)))) (P x)))) (∀ (λ x : El A, (P x)))))));
