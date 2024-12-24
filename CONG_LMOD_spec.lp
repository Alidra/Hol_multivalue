require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3070719 : Prf (∀ (λ x : El num, (∀ (λ y : El num, (∀ (λ n : El num, (= ((@== num) (MOD x n) y (num_mod n)) ((@== num) x y (num_mod n)))))))));
