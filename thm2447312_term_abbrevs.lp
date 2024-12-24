require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 (x0: El int) ≔ ((λ y0 : El int, (∀ (λ y1 : El int, (= (int_coprime ((@̦‚ int int) y0 y1)) (∃ (λ y2 : El int, (∃ (λ y3 : El int, (= (int_add (int_mul y0 y2) (int_mul y1 y3)) (int_of_num (NUMERAL (BIT1 _0)))))))))))) x0);
symbol term2 (x0: El int) (x1: El int) ≔ ((λ y0 : El int, (= (int_coprime ((@̦‚ int int) x0 y0)) (∃ (λ y1 : El int, (∃ (λ y2 : El int, (= (int_add (int_mul x0 y1) (int_mul y0 y2)) (int_of_num (NUMERAL (BIT1 _0)))))))))) x1);
symbol term1 (x0: El int) ≔ (∀ (λ y0 : El int, (= (int_coprime ((@̦‚ int int) x0 y0)) (∃ (λ y1 : El int, (∃ (λ y2 : El int, (= (int_add (int_mul x0 y1) (int_mul y0 y2)) (int_of_num (NUMERAL (BIT1 _0)))))))))));
