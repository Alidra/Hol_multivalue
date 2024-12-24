require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 (x0: El a0) (x1: El (fun num a0)) (x2: El num) ≔ ((λ y0 : El num, (= ((@FCONS a0) x0 x1 (SUC y0)) (x1 y0))) x2);
symbol term1 a0 (x0: El a0) (x1: El (fun num a0)) (x2: El num) ≔ ((@FCONS a0) x0 x1 (SUC x2));
