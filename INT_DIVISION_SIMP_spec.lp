require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2394130 : Prf (∀ (λ m : El int, (∀ (λ n : El int, (= (int_add (int_mul (div m n) n) (rem m n)) m)))));
