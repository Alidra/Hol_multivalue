require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2300691 : Prf (∀ (λ x : El int, (∀ (λ y : El int, (⇒ (int_lt (int_abs (int_sub x y)) (int_neg y)) (int_lt x (int_of_num (NUMERAL _0))))))));
