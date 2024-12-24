require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1071333 [A] (NIL' : El (recspace A)) (h1 : Prf (= NIL' ((@CONSTR A) (NUMERAL _0) ((@ε A) (λ v : El A, T)) (λ n : El num, (@BOTTOM A))))) : Prf (= (@NIL A) ((@_mk_list A) NIL'));
