require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem205347 : Prf (∧ (∀ (λ n : El num, (⇒ (EVEN n) (= (* (NUMERAL (BIT0 (BIT1 _0))) (DIV n (NUMERAL (BIT0 (BIT1 _0))))) n)))) (∀ (λ n : El num, (⇒ (EVEN n) (= (* (DIV n (NUMERAL (BIT0 (BIT1 _0)))) (NUMERAL (BIT0 (BIT1 _0)))) n)))));
