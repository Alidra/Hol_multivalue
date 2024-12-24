require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2301398 : Prf (∀ (λ x : El int, (∀ (λ k : El int, (= (∧ (int_lt (int_neg k) x) (int_lt x k)) (int_lt (int_abs x) k))))));
