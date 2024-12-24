require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1067668 [A B] : Prf (= (@INR A B) (λ a : El B, ((@_mk_sum A B) ((λ a' : El B, ((@CONSTR (prod A B)) (SUC (NUMERAL _0)) ((@̦‚ A B) ((@ε A) (λ v : El A, T)) a') (λ n : El num, (@BOTTOM (prod A B))))) a))));
