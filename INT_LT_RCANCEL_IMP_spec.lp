require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2304768 : Prf (∀ (λ x : El int, (∀ (λ y : El int, (∀ (λ z : El int, (⇒ (∧ (int_lt (int_of_num (NUMERAL _0)) z) (int_lt (int_mul x z) (int_mul y z))) (int_lt x y))))))));
