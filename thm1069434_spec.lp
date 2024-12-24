require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1069434 [A] (NONE' : El (recspace A)) (h1 : Prf (= NONE' ((@CONSTR A) (NUMERAL _0) ((@ε A) (λ v : El A, T)) (λ n : El num, (@BOTTOM A))))) : Prf (= ((@_mk_option A) NONE') ((@_mk_option A) ((@CONSTR A) (NUMERAL _0) ((@ε A) (λ v : El A, T)) (λ n : El num, (@BOTTOM A)))));
