require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1066568 [A] (a : El A) (f : El (fun num A)) : Prf ((λ f' : El (fun num A), (= ((@FCONS A) a f' (NUMERAL _0)) a)) f);
