require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1066572 [A B] (INR' : El (fun B (recspace (prod A B)))) (h1 : Prf (= INR' (λ a : El B, ((@CONSTR (prod A B)) (SUC (NUMERAL _0)) ((@̦‚ A B) ((@ε A) (λ v : El A, T)) a) (λ n : El num, (@BOTTOM (prod A B))))))) : Prf (= INR' (λ a : El B, ((@CONSTR (prod A B)) (SUC (NUMERAL _0)) ((@̦‚ A B) ((@ε A) (λ v : El A, T)) a) (λ n : El num, (@BOTTOM (prod A B))))));
