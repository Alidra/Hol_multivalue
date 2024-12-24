require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1070118 [A] (a : El A) (SOME' : El (fun A (recspace A))) (h1 : Prf (= SOME' (λ a' : El A, ((@CONSTR A) (SUC (NUMERAL _0)) a' (λ n : El num, (@BOTTOM A)))))) : Prf (= ((@SOME A) a) ((@_mk_option A) (SOME' a)));
