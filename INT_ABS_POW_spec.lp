require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2300556 : Prf (∀ (λ x : El int, (∀ (λ n : El num, (= (int_abs (int_pow x n)) (int_pow (int_abs x) n))))));
