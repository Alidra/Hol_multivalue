require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2303202 : Prf (∀ (λ x : El int, (∀ (λ y : El int, (∀ (λ z : El int, (⇒ (∧ (int_le x y) (int_le (int_of_num (NUMERAL _0)) z)) (int_le (int_mul x z) (int_mul y z)))))))));
