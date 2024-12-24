require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1595570 : Prf (∀ (λ x : El real, (∀ (λ y : El real, (∀ (λ n : El num, (= (real_pow (real_mul x y) n) (real_mul (real_pow x n) (real_pow y n)))))))));
