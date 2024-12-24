require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem359703 [A] : Prf (∀ (λ << : El (fun A (fun A bool)), (∀ (λ P : El (fun A bool), (⇒ ((@WF A) <<) ((@WF A) (λ x : El A, (λ y : El A, (∧ (P x) (∧ (P y) (<< x y)))))))))));
