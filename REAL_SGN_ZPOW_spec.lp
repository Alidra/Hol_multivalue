require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3180260 : Prf (∀ (λ x : El real, (∀ (λ n : El int, (= (real_sgn (real_zpow x n)) (real_zpow (real_sgn x) n))))));
