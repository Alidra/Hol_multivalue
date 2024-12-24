require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem316636 [A] (<< : El (fun A (fun A bool))) : Prf (= (∃ (λ P : El (fun A bool), (¬ (⇒ (∃ (λ x : El A, (P x))) (∃ (λ x : El A, (∧ (P x) (∀ (λ y : El A, (⇒ (<< y x) (¬ (P y)))))))))))) (∃ (λ s : El (fun num A), (∀ (λ n : El num, (<< (s (SUC n)) (s n)))))));
