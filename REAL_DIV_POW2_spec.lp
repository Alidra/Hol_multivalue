require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1641480 : Prf (∀ (λ x : El real, (∀ (λ m : El num, (∀ (λ n : El num, (⇒ (¬ (= x (real_of_num (NUMERAL _0)))) (= (real_div (real_pow x m) (real_pow x n)) ((@COND real) (<= n m) (real_pow x (- m n)) (real_inv (real_pow x (- n m))))))))))));
