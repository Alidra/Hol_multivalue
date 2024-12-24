require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3175238 : Prf (∀ (λ x : El real, (∀ (λ m : El int, (∀ (λ n : El int, (= (real_zpow (real_zpow x m) n) (real_zpow x (int_mul m n)))))))));
