require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 (x0: El a0) (x1: El (list a0)) ≔ ((@set_of_list a0) ((@CONS a0) x0 x1));
symbol term1 a0 (x0: El a0) (x1: El (list a0)) ≔ ((@INSERT a0) x0 ((@set_of_list a0) x1));
symbol term2 a0 (x0: El a0) (x1: El (list a0)) ≔ (∧ (= ((@set_of_list a0) (@NIL a0)) (@EMPTY a0)) (= ((@set_of_list a0) ((@CONS a0) x0 x1)) ((@INSERT a0) x0 ((@set_of_list a0) x1))));
