require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term3 (x0: El num) (x1: El num) ≔ ((@INSERT num) (SUC x1) (… x0 x1));
symbol term0 a0 (x0: El (fun a0 bool)) (x1: El (fun a0 bool)) ≔ (∀ (λ y0 : El a0, (= ((@IN a0) y0 x0) ((@IN a0) y0 x1))));
symbol term1 (x0: El (fun num bool)) (x1: El (fun num bool)) ≔ (∀ (λ y0 : El num, (= ((@IN num) y0 x0) ((@IN num) y0 x1))));
symbol term2 (x0: El num) (x1: El num) ≔ (… x0 (SUC x1));
symbol term4 (x0: El num) (x1: El num) ≔ (∀ (λ y0 : El num, (= ((@IN num) y0 (… x0 (SUC x1))) ((@IN num) y0 ((@INSERT num) (SUC x1) (… x0 x1))))));
