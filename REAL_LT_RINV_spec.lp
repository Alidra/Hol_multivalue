require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1632664 : Prf (∀ (λ x : El real, (∀ (λ y : El real, (⇒ (∧ (real_lt (real_of_num (NUMERAL _0)) x) (real_lt x (real_inv y))) (real_lt y (real_inv x)))))));
