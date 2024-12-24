require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1096523 [A] (l : El (list A)) (x : El A) : Prf ((λ x' : El A, (= ((@REVERSE A) ((@CONS A) x' l)) ((@APPEND A) ((@REVERSE A) l) ((@CONS A) x' (@NIL A))))) x);
