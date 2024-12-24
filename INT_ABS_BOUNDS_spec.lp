require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2300295 : Prf (∀ (λ x : El int, (∀ (λ k : El int, (= (int_le (int_abs x) k) (∧ (int_le (int_neg k) x) (int_le x k)))))));
