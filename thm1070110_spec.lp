require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1070110 [A] : Prf (= (@SOME A) (λ a : El A, ((@_mk_option A) ((λ a' : El A, ((@CONSTR A) (SUC (NUMERAL _0)) a' (λ n : El num, (@BOTTOM A)))) a))));
