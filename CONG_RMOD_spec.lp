require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3070799 : Prf (∀ (λ x : El num, (∀ (λ y : El num, (∀ (λ n : El num, (= ((@== num) x (MOD y n) (num_mod n)) ((@== num) x y (num_mod n)))))))));
