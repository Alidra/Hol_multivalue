require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3175418 : Prf (∀ (λ x : El real, (∀ (λ y : El real, (∀ (λ n : El int, (= (real_zpow (real_mul x y) n) (real_mul (real_zpow x n) (real_zpow y n)))))))));
