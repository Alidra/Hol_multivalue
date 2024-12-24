require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem368295 [A] : Prf (∀ (λ << : El (fun A (fun A bool)), (∀ (λ x : El A, (∀ (λ y : El A, (⇒ ((@WF A) <<) (¬ (∧ (<< x y) (<< y x))))))))));
