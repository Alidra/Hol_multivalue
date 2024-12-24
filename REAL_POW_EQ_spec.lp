require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1653383 : Prf (∀ (λ n : El num, (∀ (λ x : El real, (∀ (λ y : El real, (⇒ (∧ (¬ (= n (NUMERAL _0))) (∧ (real_le (real_of_num (NUMERAL _0)) x) (∧ (real_le (real_of_num (NUMERAL _0)) y) (= (real_pow x n) (real_pow y n))))) (= x y))))))));
