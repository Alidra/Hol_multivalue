require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2300732 : Prf (∀ (λ x : El int, (∀ (λ y : El int, (⇒ (int_lt (int_abs (int_sub x y)) (int_abs y)) (¬ (= x (int_of_num (NUMERAL _0)))))))));
