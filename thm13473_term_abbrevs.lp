require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term1 a0 (x0: El a0) (x1: El bool) (x2: El (fun a0 bool)) (x3: El a0) ≔ (∧ (⇒ x1 (x2 x0)) (⇒ (¬ x1) (x2 x3)));
symbol term0 a0 (x0: El (fun a0 bool)) (x1: El bool) (x2: El a0) (x3: El a0) ≔ (x0 ((@COND a0) x1 x2 x3));
