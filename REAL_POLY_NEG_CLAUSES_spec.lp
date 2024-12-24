require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1384312 : Prf (∧ (∀ (λ x : El real, (= (real_neg x) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 _0)))) x)))) (∀ (λ x : El real, (∀ (λ y : El real, (= (real_sub x y) (real_add x (real_mul (real_neg (real_of_num (NUMERAL (BIT1 _0)))) y))))))));
