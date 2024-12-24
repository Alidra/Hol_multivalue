require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1111469 [A] (s : El (fun num A)) (n : El num) : Prf (∧ (= ((@list_of_seq A) s (NUMERAL _0)) (@NIL A)) (= ((@list_of_seq A) s (SUC n)) ((@APPEND A) ((@list_of_seq A) s n) ((@CONS A) (s n) (@NIL A)))));
