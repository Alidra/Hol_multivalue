require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1540414 : Prf (∀ (λ x : El real, (∀ (λ y : El real, (⇒ (real_lt (real_abs (real_sub x y)) (real_abs y)) (¬ (= x (real_of_num (NUMERAL _0)))))))));
