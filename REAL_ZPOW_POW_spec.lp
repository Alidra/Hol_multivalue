require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3174260 : Prf (∧ (∀ (λ x : El real, (∀ (λ n : El num, (= (real_zpow x (int_of_num n)) (real_pow x n)))))) (∀ (λ x : El real, (∀ (λ n : El num, (= (real_zpow x (int_neg (int_of_num n))) (real_inv (real_pow x n))))))));
