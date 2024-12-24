require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2256133 : Prf (∀ (λ x : El real, (∀ (λ y : El real, (= (= (real_div x (real_add (real_of_num (NUMERAL (BIT1 _0))) (real_abs x))) y) (∧ (real_lt (real_abs y) (real_of_num (NUMERAL (BIT1 _0)))) (= (real_div y (real_sub (real_of_num (NUMERAL (BIT1 _0))) (real_abs y))) x)))))));
