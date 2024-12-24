require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2537700 : Prf (∀ (λ m : El int, (∀ (λ n : El num, (∀ (λ p : El int, (= (rem (int_pow (rem m p) n) p) (rem (int_pow m n) p))))))));
