require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1628913 : Prf (∀ (λ x : El real, (∀ (λ y : El real, (∀ (λ z : El real, (⇒ (real_lt (real_of_num (NUMERAL _0)) z) (= (real_lt x (real_div y z)) (real_lt (real_mul x z) y)))))))));
