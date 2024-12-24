require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5351259 : Prf (∀ (λ m : El num, (∀ (λ p : El num, (∀ (λ n : El num, (⇒ (∧ (<= m p) (<= p (+ n (NUMERAL (BIT1 _0))))) (= ((@UNION num) (… m (- p (NUMERAL (BIT1 _0)))) (… p n)) (… m n)))))))));
