require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2308055 : Prf (∀ (λ n : El num, (∀ (λ x : El int, (∀ (λ y : El int, (= (= (int_pow x n) (int_pow y n)) ((@COND bool) (EVEN n) (∨ (= n (NUMERAL _0)) (= (int_abs x) (int_abs y))) (= x y)))))))));
