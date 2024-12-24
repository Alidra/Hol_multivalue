require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 a1 (x0: El a1) (x1: El (fun a0 bool)) (x2: El num) (x3: El a1) (x4: El (type1411 a0 a1)) ≔ ((λ y0 : El (type1411 a0 a1), (= ((@FINREC a0 a1) y0 x0 x1 x3 (SUC x2)) (∃ (λ y1 : El a0, (∃ (λ y2 : El a1, (∧ ((@IN a0) y1 x1) (∧ ((@FINREC a0 a1) y0 x0 ((@DELETE a0) x1 y1) y2 x2) (= x3 (y0 y1 y2)))))))))) x4);
symbol term1 a0 a1 (x0: El (type1411 a0 a1)) (x1: El a1) (x2: El (fun a0 bool)) (x3: El a1) (x4: El num) ≔ ((@FINREC a0 a1) x0 x1 x2 x3 (SUC x4));
symbol term2 a0 a1 (x0: El a1) (x1: El (fun a0 bool)) (x2: El num) (x3: El a1) (x4: El (type1411 a0 a1)) ≔ (∃ (λ y0 : El a0, (∃ (λ y1 : El a1, (∧ ((@IN a0) y0 x1) (∧ ((@FINREC a0 a1) x4 x0 ((@DELETE a0) x1 y0) y1 x2) (= x3 (x4 y0 y1))))))));
