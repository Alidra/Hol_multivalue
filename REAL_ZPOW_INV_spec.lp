require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3174521 : Prf (∀ (λ x : El real, (∀ (λ n : El int, (= (real_zpow (real_inv x) n) (real_inv (real_zpow x n)))))));
