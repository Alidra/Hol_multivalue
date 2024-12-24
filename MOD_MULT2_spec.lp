require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem185837 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (∀ (λ p : El num, (= (MOD (* m n) (* m p)) (* m (MOD n p)))))))));
