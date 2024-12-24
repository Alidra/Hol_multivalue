require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1053103 : Prf (∀ (λ b : El bool, (∀ (λ x : El num, (= (NUMSUM b x) ((@COND num) b (SUC (* (NUMERAL (BIT0 (BIT1 _0))) x)) (* (NUMERAL (BIT0 (BIT1 _0))) x)))))));
