require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1606637 : Prf (∧ (∀ (λ x : El real, (∀ (λ y : El real, (⇒ (real_lt (real_of_num (NUMERAL _0)) x) (= (real_le (real_of_num (NUMERAL _0)) (real_mul x y)) (real_le (real_of_num (NUMERAL _0)) y))))))) (∀ (λ x : El real, (∀ (λ y : El real, (⇒ (real_lt (real_of_num (NUMERAL _0)) y) (= (real_le (real_of_num (NUMERAL _0)) (real_mul x y)) (real_le (real_of_num (NUMERAL _0)) x))))))));
