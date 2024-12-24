require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1069778 [A] (SOME' : El (fun A (recspace A))) (h1 : Prf (= SOME' (λ a : El A, ((@CONSTR A) (SUC (NUMERAL _0)) a (λ n : El num, (@BOTTOM A)))))) : Prf (= (λ a : El A, ((@_mk_option A) (SOME' a))) (λ a : El A, ((@_mk_option A) ((λ a' : El A, ((@CONSTR A) (SUC (NUMERAL _0)) a' (λ n : El num, (@BOTTOM A)))) a))));
