require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term1 (x0: El (fun 1 bool)) ≔ (∀ (λ y0 : El 1, (x0 y0)));
symbol term0 (x0: El (fun 1 bool)) ≔ (∧ (⇒ (∀ (λ y0 : El 1, (x0 y0))) (x0 one)) (⇒ (x0 one) (∀ (λ y0 : El 1, (x0 y0)))));
