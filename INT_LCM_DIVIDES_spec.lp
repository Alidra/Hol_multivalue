require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2826831 : Prf (∀ (λ m : El int, (∀ (λ n : El int, (∀ (λ d : El int, (= (int_divides (int_lcm ((@̦‚ int int) m n)) d) (∧ (int_divides m d) (int_divides n d)))))))));
