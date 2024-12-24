require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1584226 : Prf (∀ (λ x : El real, (∀ (λ y : El real, (∀ (λ z : El real, (⇒ (∧ (real_le x y) (real_le (real_of_num (NUMERAL _0)) z)) (real_le (real_mul x z) (real_mul y z)))))))));
