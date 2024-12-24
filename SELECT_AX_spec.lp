require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem9221 [A] : Prf (∀ (λ P : El (fun A bool), (∀ (λ x : El A, (⇒ (P x) (P ((@ε A) P)))))));
