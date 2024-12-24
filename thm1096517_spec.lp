require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1096517 [A] : Prf (∧ (= ((@REVERSE A) (@NIL A)) (@NIL A)) (∀ (λ l : El (list A), (∀ (λ x : El A, (= ((@REVERSE A) ((@CONS A) x l)) ((@APPEND A) ((@REVERSE A) l) ((@CONS A) x (@NIL A)))))))));
