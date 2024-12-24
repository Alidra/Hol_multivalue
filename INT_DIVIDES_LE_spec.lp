require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2436585 : Prf (∀ (λ x : El int, (∀ (λ y : El int, (⇒ (int_divides x y) (∨ (int_le (int_abs x) (int_abs y)) (= y (int_of_num (NUMERAL _0)))))))));
