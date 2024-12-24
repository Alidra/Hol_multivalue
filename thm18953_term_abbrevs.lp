require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term2 a0 (x0: El (fun a0 bool)) (x1: El (fun a0 bool)) ≔ (∧ (∀ (λ y0 : El a0, (x0 y0))) (∀ (λ y0 : El a0, (x1 y0))));
symbol term1 a0 (x0: El (fun a0 bool)) (x1: El (fun a0 bool)) ≔ (∀ (λ y0 : El a0, (∧ (x0 y0) (x1 y0))));
symbol term0 a0 (x0: El (fun a0 bool)) (x1: El (fun a0 bool)) ≔ ((λ y0 : El (fun a0 bool), (= (∀ (λ y1 : El a0, (∧ (x0 y1) (y0 y1)))) (∧ (∀ (λ y1 : El a0, (x0 y1))) (∀ (λ y1 : El a0, (y0 y1)))))) x1);
