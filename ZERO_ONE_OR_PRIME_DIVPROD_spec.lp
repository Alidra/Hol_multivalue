require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3157314 : Prf (∀ (λ p : El num, (∀ (λ a : El num, (∀ (λ b : El num, (⇒ (∨ (= p (NUMERAL _0)) (∨ (= p (NUMERAL (BIT1 _0))) (prime p))) (= (num_divides p (* a b)) (∨ (num_divides p a) (num_divides p b))))))))));
