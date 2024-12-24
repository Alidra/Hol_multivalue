require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1632888 : Prf (∀ (λ x : El real, (∀ (λ y : El real, (⇒ (∧ (real_lt (real_of_num (NUMERAL _0)) x) (real_le x (real_inv y))) (real_le y (real_inv x)))))));
