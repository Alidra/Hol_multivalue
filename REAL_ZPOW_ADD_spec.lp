require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3179019 : Prf (∀ (λ x : El real, (∀ (λ m : El int, (∀ (λ n : El int, (⇒ (¬ (= x (real_of_num (NUMERAL _0)))) (= (real_zpow x (int_add m n)) (real_mul (real_zpow x m) (real_zpow x n))))))))));
