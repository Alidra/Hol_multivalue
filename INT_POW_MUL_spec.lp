require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2308770 : Prf (∀ (λ x : El int, (∀ (λ y : El int, (∀ (λ n : El num, (= (int_pow (int_mul x y) n) (int_mul (int_pow x n) (int_pow y n)))))))));
