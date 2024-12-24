require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3175506 : Prf (∀ (λ x : El real, (∀ (λ y : El real, (∀ (λ n : El int, (= (real_zpow (real_div x y) n) (real_div (real_zpow x n) (real_zpow y n)))))))));
