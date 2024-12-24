require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2829046 : Prf (∀ (λ m : El int, (∀ (λ n : El int, (∧ (int_divides m (int_lcm ((@̦‚ int int) m n))) (∧ (int_divides n (int_lcm ((@̦‚ int int) m n))) (∀ (λ d : El int, (⇒ (∧ (int_divides m d) (int_divides n d)) (int_divides (int_lcm ((@̦‚ int int) m n)) d))))))))));
