require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1067330 [A B] : Prf (= (@INL A B) (λ a : El A, ((@_mk_sum A B) ((λ a' : El A, ((@CONSTR (prod A B)) (NUMERAL _0) ((@̦‚ A B) a' ((@ε B) (λ v : El B, T))) (λ n : El num, (@BOTTOM (prod A B))))) a))));
