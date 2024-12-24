require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4383326 [A B] : Prf (= ((@EXTENSIONAL A B) (@EMPTY A)) ((@INSERT (fun A B)) (λ x : El A, (@ARB B)) (@EMPTY (fun A B))));
