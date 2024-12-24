require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term1 a0 a1 (x0: El (fun a0 bool)) (x1: El a1) (x2: El a1) ≔ (∧ (= x0 (@EMPTY a0)) (= x1 x2));
symbol term0 a0 a1 (x0: El (type1411 a0 a1)) (x1: El a1) (x2: El (fun a0 bool)) (x3: El a1) ≔ ((@FINREC a0 a1) x0 x1 x2 x3 (NUMERAL _0));
