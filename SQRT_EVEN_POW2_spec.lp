require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1964708 : Prf (∀ (λ n : El num, (⇒ (EVEN n) (= (sqrt (real_pow (real_of_num (NUMERAL (BIT0 (BIT1 _0)))) n)) (real_pow (real_of_num (NUMERAL (BIT0 (BIT1 _0)))) (DIV n (NUMERAL (BIT0 (BIT1 _0)))))))));
