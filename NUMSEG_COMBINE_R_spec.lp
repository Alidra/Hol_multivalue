require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5336704 : Prf (∀ (λ m : El num, (∀ (λ p : El num, (∀ (λ n : El num, (⇒ (∧ (<= m (+ p (NUMERAL (BIT1 _0)))) (<= p n)) (= ((@UNION num) (… m p) (… (+ p (NUMERAL (BIT1 _0))) n)) (… m n)))))))));
