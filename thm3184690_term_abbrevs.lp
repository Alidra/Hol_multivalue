require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 (x0: El a0) (x1: El (fun a0 bool)) ≔ (∃ (λ y0 : El a0, ((@SETSPEC a0) x0 (x1 y0) y0)));
