require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2532785 : Prf (∀ (λ n : El int, (∀ (λ p : El int, (= (rem (int_neg (rem n p)) p) (rem (int_neg n) p))))));
