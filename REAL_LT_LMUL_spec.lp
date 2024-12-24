require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1584766 : Prf (∀ (λ x : El real, (∀ (λ y : El real, (∀ (λ z : El real, (⇒ (∧ (real_lt (real_of_num (NUMERAL _0)) x) (real_lt y z)) (real_lt (real_mul x y) (real_mul x z)))))))));
