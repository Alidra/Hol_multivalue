require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1629051 : Prf (∀ (λ x : El real, (∀ (λ y : El real, (∀ (λ z : El real, (⇒ (real_lt (real_of_num (NUMERAL _0)) z) (= (real_lt (real_div x z) y) (real_lt x (real_mul y z))))))))));
