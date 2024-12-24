require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term1 a0 (x0: El a0) (x1: El (fun a0 bool)) (x2: El (list a0)) ≔ (∧ (x1 x0) ((@ALL a0) x1 x2));
symbol term2 a0 (x0: El a0) (x1: El (fun a0 bool)) (x2: El (list a0)) ≔ (∧ (= ((@ALL a0) x1 (@NIL a0)) T) (= ((@ALL a0) x1 ((@CONS a0) x0 x2)) (∧ (x1 x0) ((@ALL a0) x1 x2))));
symbol term0 a0 (x0: El (fun a0 bool)) (x1: El a0) (x2: El (list a0)) ≔ ((@ALL a0) x0 ((@CONS a0) x1 x2));
