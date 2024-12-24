require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem15306 : Prf (∀ (λ P : El (fun bool bool), (⇒ (∧ (P F) (P T)) (∀ (λ x : El bool, (P x))))));
