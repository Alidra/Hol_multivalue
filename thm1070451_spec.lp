require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1070451 [A] (CONS' : El (fun A (fun (recspace A) (recspace A)))) (h1 : Prf (= CONS' (λ a0 : El A, (λ a1 : El (recspace A), ((@CONSTR A) (SUC (NUMERAL _0)) a0 ((@FCONS (recspace A)) a1 (λ n : El num, (@BOTTOM A)))))))) : Prf (= CONS' (λ a0 : El A, (λ a1 : El (recspace A), ((@CONSTR A) (SUC (NUMERAL _0)) a0 ((@FCONS (recspace A)) a1 (λ n : El num, (@BOTTOM A)))))));
