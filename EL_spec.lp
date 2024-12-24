require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1105750 [_25569] (n : El num) (l : El (list _25569)) : Prf (∧ (= ((@EL _25569) (NUMERAL _0) l) ((@HD _25569) l)) (= ((@EL _25569) (SUC n) l) ((@EL _25569) n ((@TL _25569) l))));
