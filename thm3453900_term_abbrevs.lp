require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term2 a0 (x0: El (type686 a0)) (x1: El a0) ≔ (∃ (λ y0 : El (fun a0 bool), (∧ ((@IN (fun a0 bool)) y0 x0) ((@IN a0) x1 y0))));
symbol term1 a0 (x0: El a0) (x1: El (type686 a0)) ≔ ((@IN a0) x0 ((@UNIONS a0) x1));
symbol term0 a0 (x0: El (type686 a0)) (x1: El a0) ≔ ((λ y0 : El a0, (= ((@IN a0) y0 ((@UNIONS a0) x0)) (∃ (λ y1 : El (fun a0 bool), (∧ ((@IN (fun a0 bool)) y1 x0) ((@IN a0) y0 y1)))))) x1);
