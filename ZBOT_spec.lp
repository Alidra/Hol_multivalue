require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1058228 [A] : Prf (= (@ZBOT A) ((@INJP A) ((@INJN A) (NUMERAL _0)) ((@ε (fun num (fun A bool))) (λ z : El (fun num (fun A bool)), T))));
