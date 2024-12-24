require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2530600 (m : El int) : Prf (∀ (λ n : El int, (∀ (λ p : El int, (= (rem (rem m (int_mul n p)) n) (rem m n))))));
