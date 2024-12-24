require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3138346 : Prf (∀ (λ p : El num, (= (∨ (= p (NUMERAL (BIT1 _0))) (prime p)) (∀ (λ n : El num, (⇒ (num_divides n p) (∨ (= n (NUMERAL (BIT1 _0))) (= n p))))))));
