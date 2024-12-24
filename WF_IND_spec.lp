require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem309906 [A] (<< : El (fun A (fun A bool))) : Prf (= ((@WF A) <<) (∀ (λ P : El (fun A bool), (⇒ (∀ (λ x : El A, (⇒ (∀ (λ y : El A, (⇒ (<< y x) (P y)))) (P x)))) (∀ (λ x : El A, (P x)))))));
