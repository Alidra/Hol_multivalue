require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term2 (x0: El real) (x1: El real) ≔ ((λ y0 : El real, (= (¬ (= x0 y0)) (∃ (λ y1 : El real, (= (real_mul (real_sub x0 y0) y1) (real_of_num (NUMERAL (BIT1 _0)))))))) x1);
symbol term1 (x0: El real) ≔ (∀ (λ y0 : El real, (= (¬ (= x0 y0)) (∃ (λ y1 : El real, (= (real_mul (real_sub x0 y0) y1) (real_of_num (NUMERAL (BIT1 _0)))))))));
symbol term0 (x0: El real) ≔ ((λ y0 : El real, (∀ (λ y1 : El real, (= (¬ (= y0 y1)) (∃ (λ y2 : El real, (= (real_mul (real_sub y0 y1) y2) (real_of_num (NUMERAL (BIT1 _0)))))))))) x0);
