require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem181826 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (⇒ (∧ (< (NUMERAL _0) m) (<= m n)) (<= (* (NUMERAL (BIT0 (BIT1 _0))) (MOD n m)) n))))));
