require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2806007 : Prf (∀ (λ d : El int, (∀ (λ n : El int, (= (int_divides d (int_abs n)) (int_divides d n))))));
