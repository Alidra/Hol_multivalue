require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2835460 : Prf (∀ (λ x : El int, (∀ (λ y : El int, (⇒ (∧ (int_le (int_of_num (NUMERAL _0)) x) (int_le (int_of_num (NUMERAL _0)) y)) (= (num_of_int (int_add x y)) (+ (num_of_int x) (num_of_int y))))))));
