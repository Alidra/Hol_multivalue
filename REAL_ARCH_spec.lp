require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1700438 : Prf (∀ (λ x : El real, (⇒ (real_lt (real_of_num (NUMERAL _0)) x) (∀ (λ y : El real, (∃ (λ n : El num, (real_lt y (real_mul (real_of_num n) x)))))))));
