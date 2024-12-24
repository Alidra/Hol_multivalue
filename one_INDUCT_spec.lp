require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem16018 : Prf (∀ (λ P : El (fun 1 bool), (⇒ (P one) (∀ (λ x : El 1, (P x))))));
