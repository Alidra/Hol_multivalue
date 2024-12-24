require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2302816 : Prf (∀ (λ w : El int, (∀ (λ x : El int, (∀ (λ y : El int, (∀ (λ z : El int, (⇒ (∧ (int_le (int_of_num (NUMERAL _0)) w) (∧ (int_le w x) (∧ (int_le (int_of_num (NUMERAL _0)) y) (int_le y z)))) (int_le (int_mul w y) (int_mul x z)))))))))));
