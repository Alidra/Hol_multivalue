require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3130395 : Prf (∀ (λ x : El int, (∀ (λ y : El int, (⇒ (⇒ (= y (int_of_num (NUMERAL _0))) (int_le (int_of_num (NUMERAL _0)) x)) (∃ (λ n : El num, ((@== int) (int_of_num n) x (int_mod y)))))))));
