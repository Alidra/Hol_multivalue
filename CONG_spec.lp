require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3070637 : Prf (∀ (λ x : El num, (∀ (λ y : El num, (∀ (λ n : El num, (= ((@== num) x y (num_mod n)) (= (MOD x n) (MOD y n)))))))));
