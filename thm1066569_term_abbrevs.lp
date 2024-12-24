require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 (x0: El a0) (x1: El (fun num a0)) ≔ ((λ y0 : El (fun num a0), (= ((@FCONS a0) x0 y0 (NUMERAL _0)) x0)) x1);
symbol term1 a0 (x0: El a0) (x1: El (fun num a0)) ≔ ((@FCONS a0) x0 x1 (NUMERAL _0));
