require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1629611 : Prf (∀ (λ x : El real, (∀ (λ y : El real, (∀ (λ z : El real, (⇒ (real_lt (real_of_num (NUMERAL _0)) z) (= (real_lt (real_div x z) (real_div y z)) (real_lt x y)))))))));
