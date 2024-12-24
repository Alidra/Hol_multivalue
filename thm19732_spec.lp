require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem19732 [A] (P : El (fun A bool)) : Prf (∀ (λ x : El A, (⇒ (P x) (P ((@ε A) P)))));
