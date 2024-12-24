require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem369021 [A] (<< : El (fun A (fun A bool))) : Prf (∀ (λ x : El A, (⇒ ((@WF A) <<) (¬ (<< x x)))));
