require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 (x0: El real) ≔ (∀ (λ y0 : El num, (= (real_pow x0 (SUC y0)) (real_mul x0 (real_pow x0 y0)))));
symbol term1 (x0: El real) ≔ (∧ (= (real_pow x0 (NUMERAL _0)) (real_of_num (NUMERAL (BIT1 _0)))) (∀ (λ y0 : El num, (= (real_pow x0 (SUC y0)) (real_mul x0 (real_pow x0 y0))))));
