require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3133024 : Prf (∀ (λ a : El num, (∀ (λ b : El num, (∧ (∧ (num_divides (num_gcd ((@̦‚ num num) a b)) a) (num_divides (num_gcd ((@̦‚ num num) a b)) b)) (∀ (λ e : El num, (⇒ (∧ (num_divides e a) (num_divides e b)) (num_divides e (num_gcd ((@̦‚ num num) a b)))))))))));
