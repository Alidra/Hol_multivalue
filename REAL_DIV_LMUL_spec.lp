require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1593226 : Prf (∀ (λ x : El real, (∀ (λ y : El real, (⇒ (¬ (= y (real_of_num (NUMERAL _0)))) (= (real_mul y (real_div x y)) x))))));
