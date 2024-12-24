require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2816478 : Prf (∀ (λ m : El int, (∀ (λ n : El int, (∀ (λ d : El int, (= (int_divides d (int_lcm ((@̦‚ int int) m n))) (int_divides (int_mul d (int_gcd ((@̦‚ int int) m n))) (int_mul m n)))))))));
