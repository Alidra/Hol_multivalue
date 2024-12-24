require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem184261 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (⇒ (EVEN n) (= (MOD (MOD m n) (NUMERAL (BIT0 (BIT1 _0)))) (MOD m (NUMERAL (BIT0 (BIT1 _0))))))))));
