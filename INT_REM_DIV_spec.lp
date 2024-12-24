require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2400155 : Prf (∀ (λ m : El int, (∀ (λ n : El int, (= (rem m n) (int_sub m (int_mul (div m n) n)))))));
