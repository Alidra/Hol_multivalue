require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1554983 : Prf (∀ (λ x : El real, (∀ (λ k : El real, (= (∧ (real_lt (real_neg k) x) (real_lt x k)) (real_lt (real_abs x) k))))));
