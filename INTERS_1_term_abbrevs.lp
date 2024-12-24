require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 (x0: El (fun a0 bool)) ≔ ((@INTERS a0) ((@INSERT (fun a0 bool)) x0 (@EMPTY (fun a0 bool))));
