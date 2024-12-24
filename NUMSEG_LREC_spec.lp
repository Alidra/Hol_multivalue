require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5357842 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (⇒ (<= m n) (= ((@INSERT num) m (… (+ m (NUMERAL (BIT1 _0))) n)) (… m n)))))));
