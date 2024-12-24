require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term1 a0 a1 (x0: El a1) (x1: El (fun a0 a1)) (x2: El (fun a0 bool)) ≔ ((@IN a1) x0 ((@IMAGE a0 a1) x1 x2));
symbol term0 a0 a1 (x0: El a1) (x1: El (fun a0 bool)) (x2: El (fun a0 a1)) ≔ ((λ y0 : El (fun a0 a1), (= ((@IN a1) x0 ((@IMAGE a0 a1) y0 x1)) (∃ (λ y1 : El a0, (∧ (= x0 (y0 y1)) ((@IN a0) y1 x1)))))) x2);
symbol term2 a0 a1 (x0: El a1) (x1: El (fun a0 a1)) (x2: El (fun a0 bool)) ≔ (∃ (λ y0 : El a0, (∧ (= x0 (x1 y0)) ((@IN a0) y0 x2))));
