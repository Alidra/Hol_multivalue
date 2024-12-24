require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4793256 [A] : Prf (∀ (λ a : El A, (= ((@list_of_set A) ((@INSERT A) a (@EMPTY A))) ((@CONS A) a (@NIL A)))));
