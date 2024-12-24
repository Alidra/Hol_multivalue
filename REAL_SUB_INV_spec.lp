require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1634063 : Prf (∀ (λ x : El real, (∀ (λ y : El real, (⇒ (∧ (¬ (= x (real_of_num (NUMERAL _0)))) (¬ (= y (real_of_num (NUMERAL _0))))) (= (real_sub (real_inv x) (real_inv y)) (real_div (real_sub y x) (real_mul x y))))))));
