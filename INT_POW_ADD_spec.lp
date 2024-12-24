require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2307775 : Prf (∀ (λ x : El int, (∀ (λ m : El num, (∀ (λ n : El num, (= (int_pow x (+ m n)) (int_mul (int_pow x m) (int_pow x n)))))))));
