require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4785473 [A] (h : El A) (t : El (list A)) : Prf (∧ (= ((@set_of_list A) (@NIL A)) (@EMPTY A)) (= ((@set_of_list A) ((@CONS A) h t)) ((@INSERT A) h ((@set_of_list A) t))));
