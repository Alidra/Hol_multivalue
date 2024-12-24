require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1669003 : Prf (∀ (λ n : El num, (∀ (λ x : El real, (∀ (λ y : El real, (= (= (real_pow x n) (real_pow y n)) ((@COND bool) (EVEN n) (∨ (= n (NUMERAL _0)) (= (real_abs x) (real_abs y))) (= x y)))))))));
