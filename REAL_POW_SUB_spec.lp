require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1598415 : Prf (∀ (λ x : El real, (∀ (λ m : El num, (∀ (λ n : El num, (⇒ (∧ (¬ (= x (real_of_num (NUMERAL _0)))) (<= m n)) (= (real_pow x (- n m)) (real_div (real_pow x n) (real_pow x m))))))))));
