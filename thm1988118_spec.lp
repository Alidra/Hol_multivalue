require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1988118 : Prf (∀ (λ x : El real, (∀ (λ y : El real, (= (¬ (= x y)) (∃ (λ z : El real, (= (real_mul (real_sub x y) z) (real_of_num (NUMERAL (BIT1 _0)))))))))));
