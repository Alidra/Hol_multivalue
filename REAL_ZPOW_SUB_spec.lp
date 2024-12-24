require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3179167 : Prf (∀ (λ x : El real, (∀ (λ m : El int, (∀ (λ n : El int, (⇒ (¬ (= x (real_of_num (NUMERAL _0)))) (= (real_zpow x (int_sub m n)) (real_div (real_zpow x m) (real_zpow x n))))))))));
