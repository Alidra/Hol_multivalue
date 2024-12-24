require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1067682 [A B] (a : El B) (INR' : El (fun B (recspace (prod A B)))) (h1 : Prf (= INR' (λ a' : El B, ((@CONSTR (prod A B)) (SUC (NUMERAL _0)) ((@̦‚ A B) ((@ε A) (λ v : El A, T)) a') (λ n : El num, (@BOTTOM (prod A B))))))) : Prf (= ((@INR A B) a) ((@_mk_sum A B) (INR' a)));
