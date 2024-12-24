require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1066569 [A] (f : El (fun num A)) (a : El A) : Prf (= ((λ f' : El (fun num A), (= ((@FCONS A) a f' (NUMERAL _0)) a)) f) (= ((@FCONS A) a f (NUMERAL _0)) a));
