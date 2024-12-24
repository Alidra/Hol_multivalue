require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1594665 : Prf (∀ (λ x : El real, (∀ (λ y : El real, (= (= (real_div x y) (real_of_num (NUMERAL (BIT1 _0)))) (∧ (= x y) (∧ (¬ (= x (real_of_num (NUMERAL _0)))) (¬ (= y (real_of_num (NUMERAL _0)))))))))));
