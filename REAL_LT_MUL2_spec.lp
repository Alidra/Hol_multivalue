require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1630835 : Prf (∀ (λ w : El real, (∀ (λ x : El real, (∀ (λ y : El real, (∀ (λ z : El real, (⇒ (∧ (real_le (real_of_num (NUMERAL _0)) w) (∧ (real_lt w x) (∧ (real_le (real_of_num (NUMERAL _0)) y) (real_lt y z)))) (real_lt (real_mul w y) (real_mul x z)))))))))));
