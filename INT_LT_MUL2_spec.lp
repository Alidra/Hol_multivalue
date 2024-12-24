require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2304463 : Prf (∀ (λ w : El int, (∀ (λ x : El int, (∀ (λ y : El int, (∀ (λ z : El int, (⇒ (∧ (int_le (int_of_num (NUMERAL _0)) w) (∧ (int_lt w x) (∧ (int_le (int_of_num (NUMERAL _0)) y) (int_lt y z)))) (int_lt (int_mul w y) (int_mul x z)))))))))));
