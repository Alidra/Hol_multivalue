require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3173052 : Prf (∀ (λ x : El real, (∀ (λ n : El int, (= (real_zpow x (int_neg n)) (real_inv (real_zpow x n)))))));
