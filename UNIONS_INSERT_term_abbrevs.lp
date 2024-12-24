require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term1 a0 (x0: El (fun a0 bool)) (x1: El (type686 a0)) ≔ ((@UNION a0) x0 ((@UNIONS a0) x1));
symbol term0 a0 (x0: El (fun a0 bool)) (x1: El (type686 a0)) ≔ ((@UNIONS a0) ((@INSERT (fun a0 bool)) x0 x1));
