require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2447313 (a : El int) (b : El int) : Prf (= ((λ b' : El int, (= (int_coprime ((@̦‚ int int) a b')) (∃ (λ x : El int, (∃ (λ y : El int, (= (int_add (int_mul a x) (int_mul b' y)) (int_of_num (NUMERAL (BIT1 _0)))))))))) b) (= (int_coprime ((@̦‚ int int) a b)) (∃ (λ x : El int, (∃ (λ y : El int, (= (int_add (int_mul a x) (int_mul b y)) (int_of_num (NUMERAL (BIT1 _0))))))))));
