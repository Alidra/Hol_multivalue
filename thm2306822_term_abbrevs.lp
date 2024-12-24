require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 ≔ (∧ (∀ (λ y0 : El num, (∀ (λ y1 : El num, (= (real_min (real_of_num y0) (real_of_num y1)) (real_of_num (MIN y0 y1))))))) (∧ (∀ (λ y0 : El num, (∀ (λ y1 : El num, (= (real_add (real_of_num y0) (real_of_num y1)) (real_of_num (+ y0 y1))))))) (∧ (∀ (λ y0 : El num, (∀ (λ y1 : El num, (= (real_mul (real_of_num y0) (real_of_num y1)) (real_of_num (* y0 y1))))))) (∀ (λ y0 : El num, (∀ (λ y1 : El num, (= (real_pow (real_of_num y0) y1) (real_of_num (EXP y0 y1))))))))));
