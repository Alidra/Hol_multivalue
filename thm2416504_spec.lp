require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2416504 : Prf (∧ (∀ (λ x : El int, (= (int_neg x) (int_mul (int_neg (int_of_num (NUMERAL (BIT1 _0)))) x)))) (∀ (λ x : El int, (∀ (λ y : El int, (= (int_sub x y) (int_add x (int_mul (int_neg (int_of_num (NUMERAL (BIT1 _0)))) y))))))));
