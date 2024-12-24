require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1111460 [A] (s : El (fun num A)) : Prf ((λ s' : El (fun num A), (= ((@list_of_seq A) s' (NUMERAL _0)) (@NIL A))) s);
