require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3137997 : Prf (∀ (λ p : El num, (= (prime p) (∧ (¬ (= p (NUMERAL (BIT1 _0)))) (∀ (λ x : El num, (⇒ (num_divides x p) (∨ (= x (NUMERAL (BIT1 _0))) (= x p)))))))));
