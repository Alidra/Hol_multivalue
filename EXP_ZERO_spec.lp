require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem87446 : Prf (∀ (λ n : El num, (= (EXP (NUMERAL _0) n) ((@COND num) (= n (NUMERAL _0)) (NUMERAL (BIT1 _0)) (NUMERAL _0)))));
