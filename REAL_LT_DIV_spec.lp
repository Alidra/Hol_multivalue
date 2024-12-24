require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1640961 : Prf (∀ (λ x : El real, (∀ (λ y : El real, (⇒ (∧ (real_lt (real_of_num (NUMERAL _0)) x) (real_lt (real_of_num (NUMERAL _0)) y)) (real_lt (real_of_num (NUMERAL _0)) (real_div x y)))))));
