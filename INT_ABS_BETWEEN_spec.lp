require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2300082 : Prf (∀ (λ x : El int, (∀ (λ y : El int, (∀ (λ d : El int, (= (∧ (int_lt (int_of_num (NUMERAL _0)) d) (∧ (int_lt (int_sub x d) y) (int_lt y (int_add x d)))) (int_lt (int_abs (int_sub y x)) d))))))));
