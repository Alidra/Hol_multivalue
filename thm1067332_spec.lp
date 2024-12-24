require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1067332 [A B] (INL' : El (fun A (recspace (prod A B)))) (h1 : Prf (= INL' (λ a : El A, ((@CONSTR (prod A B)) (NUMERAL _0) ((@̦‚ A B) a ((@ε B) (λ v : El B, T))) (λ n : El num, (@BOTTOM (prod A B))))))) : Prf (= (@INL A B) (λ a : El A, ((@_mk_sum A B) (INL' a))));
