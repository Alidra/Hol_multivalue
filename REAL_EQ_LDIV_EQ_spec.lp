require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1629489 : Prf (∀ (λ x : El real, (∀ (λ y : El real, (∀ (λ z : El real, (⇒ (real_lt (real_of_num (NUMERAL _0)) z) (= (= (real_div x z) y) (= x (real_mul y z))))))))));
