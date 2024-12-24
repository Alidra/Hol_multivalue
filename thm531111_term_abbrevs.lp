require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 ≔ (∧ (∀ (λ y0 : El num, (∀ (λ y1 : El num, (= (+ (BIT0 y0) (BIT1 y1)) (BIT1 (+ y0 y1))))))) (∧ (∀ (λ y0 : El num, (∀ (λ y1 : El num, (= (+ (BIT1 y0) (BIT0 y1)) (BIT1 (+ y0 y1))))))) (∀ (λ y0 : El num, (∀ (λ y1 : El num, (= (+ (BIT1 y0) (BIT1 y1)) (BIT0 (SUC (+ y0 y1))))))))));
symbol term1 ≔ (∀ (λ y0 : El num, (∀ (λ y1 : El num, (= (+ (BIT0 y0) (BIT1 y1)) (BIT1 (+ y0 y1)))))));
symbol term3 (x0: El num) ≔ (∀ (λ y0 : El num, (= (+ (BIT0 x0) (BIT1 y0)) (BIT1 (+ x0 y0)))));
symbol term2 (x0: El num) ≔ ((λ y0 : El num, (∀ (λ y1 : El num, (= (+ (BIT0 y0) (BIT1 y1)) (BIT1 (+ y0 y1)))))) x0);
symbol term4 (x0: El num) (x1: El num) ≔ ((λ y0 : El num, (= (+ (BIT0 x0) (BIT1 y0)) (BIT1 (+ x0 y0)))) x1);
