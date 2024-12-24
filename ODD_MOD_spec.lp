require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem202889 : Prf (∀ (λ n : El num, (= (ODD n) (= (MOD n (NUMERAL (BIT0 (BIT1 _0)))) (NUMERAL (BIT1 _0))))));
