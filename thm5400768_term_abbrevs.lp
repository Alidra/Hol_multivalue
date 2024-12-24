require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term2 a0 (x0: El a0) (x1: El a0) (x2: El (fun a0 bool)) ≔ (∨ (= x1 x0) ((@IN a0) x1 x2));
symbol term1 a0 (x0: El a0) (x1: El a0) (x2: El (fun a0 bool)) ≔ ((@IN a0) x0 ((@INSERT a0) x1 x2));
symbol term0 a0 (x0: El a0) (x1: El a0) (x2: El (fun a0 bool)) ≔ ((λ y0 : El (fun a0 bool), (= ((@IN a0) x1 ((@INSERT a0) x0 y0)) (∨ (= x1 x0) ((@IN a0) x1 y0)))) x2);
