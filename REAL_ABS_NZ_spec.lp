require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1534492 : Prf (∀ (λ x : El real, (= (¬ (= x (real_of_num (NUMERAL _0)))) (real_lt (real_of_num (NUMERAL _0)) (real_abs x)))));
