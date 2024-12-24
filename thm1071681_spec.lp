require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1071681 [A] : Prf (= (@CONS A) (λ a0 : El A, (λ a1 : El (list A), ((@_mk_list A) ((λ a0' : El A, (λ a1' : El (recspace A), ((@CONSTR A) (SUC (NUMERAL _0)) a0' ((@FCONS (recspace A)) a1' (λ n : El num, (@BOTTOM A)))))) a0 ((@_dest_list A) a1))))));
