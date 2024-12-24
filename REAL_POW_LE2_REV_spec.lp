require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1650795 : Prf (∀ (λ n : El num, (∀ (λ x : El real, (∀ (λ y : El real, (⇒ (∧ (¬ (= n (NUMERAL _0))) (∧ (real_le (real_of_num (NUMERAL _0)) y) (real_le (real_pow x n) (real_pow y n)))) (real_le x y))))))));
