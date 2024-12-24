require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2304244 : Prf (∀ (λ x : El int, (∀ (λ y : El int, (∀ (λ z : El int, (⇒ (int_lt (int_of_num (NUMERAL _0)) z) (= (int_lt (int_mul z x) (int_mul z y)) (int_lt x y)))))))));
