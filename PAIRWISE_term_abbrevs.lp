require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term2 a0 (x0: El a0) (x1: El (type1402 a0)) (x2: El (list a0)) ≔ (∧ (= ((@PAIRWISE a0) x1 (@NIL a0)) T) (= ((@PAIRWISE a0) x1 ((@CONS a0) x0 x2)) (∧ ((@ALL a0) (x1 x0) x2) ((@PAIRWISE a0) x1 x2))));
symbol term0 a0 (x0: El (type1402 a0)) (x1: El a0) (x2: El (list a0)) ≔ ((@PAIRWISE a0) x0 ((@CONS a0) x1 x2));
symbol term1 a0 (x0: El a0) (x1: El (type1402 a0)) (x2: El (list a0)) ≔ (∧ ((@ALL a0) (x1 x0) x2) ((@PAIRWISE a0) x1 x2));
