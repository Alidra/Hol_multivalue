require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2804399 : Prf (∀ (λ d : El int, (∀ (λ n : El int, (= (int_divides (int_abs d) n) (int_divides d n))))));
