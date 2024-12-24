require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem16264 (P : El (fun 1 bool)) : Prf (∧ (⇒ (∀ (λ x : El 1, (P x))) (P one)) (⇒ (P one) (∀ (λ x : El 1, (P x)))));
