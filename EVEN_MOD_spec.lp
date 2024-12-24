require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem201634 : Prf (∀ (λ n : El num, (= (EVEN n) (= (MOD n (NUMERAL (BIT0 (BIT1 _0)))) (NUMERAL _0)))));
