require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1553652 : Prf (∀ (λ x : El real, (∀ (λ k : El real, (= (∧ (real_le (real_neg k) x) (real_le x k)) (real_le (real_abs x) k))))));
