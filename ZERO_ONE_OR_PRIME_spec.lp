require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3168281 : Prf (∀ (λ p : El num, (= (∨ (= p (NUMERAL _0)) (∨ (= p (NUMERAL (BIT1 _0))) (prime p))) (∀ (λ a : El num, (∀ (λ b : El num, (⇒ (num_divides p (* a b)) (∨ (num_divides p a) (num_divides p b))))))))));
