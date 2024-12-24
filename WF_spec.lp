require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem303045 [A] : Prf (∀ (λ << : El (fun A (fun A bool)), (= ((@WF A) <<) (∀ (λ P : El (fun A bool), (⇒ (∃ (λ x : El A, (P x))) (∃ (λ x : El A, (∧ (P x) (∀ (λ y : El A, (⇒ (<< y x) (¬ (P y))))))))))))));
