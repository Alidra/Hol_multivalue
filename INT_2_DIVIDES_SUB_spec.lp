require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2745113 : Prf (∀ (λ m : El int, (∀ (λ n : El int, (= (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 _0)))) (int_sub m n)) (= (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 _0)))) m) (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 _0)))) n)))))));
