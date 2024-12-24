require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1596102 : Prf (∀ (λ x : El real, (∀ (λ m : El num, (∀ (λ n : El num, (= (real_pow x (+ m n)) (real_mul (real_pow x m) (real_pow x n)))))))));
