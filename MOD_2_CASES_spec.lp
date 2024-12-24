require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem204487 : Prf (∀ (λ n : El num, (= (MOD n (NUMERAL (BIT0 (BIT1 _0)))) ((@COND num) (EVEN n) (NUMERAL _0) (NUMERAL (BIT1 _0))))));
