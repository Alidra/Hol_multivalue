require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 ≔ (∧ (= (+ _0 _0) _0) (∧ (∀ (λ y0 : El num, (= (+ _0 (BIT0 y0)) (BIT0 y0)))) (∧ (∀ (λ y0 : El num, (= (+ _0 (BIT1 y0)) (BIT1 y0)))) (∧ (∀ (λ y0 : El num, (= (+ (BIT0 y0) _0) (BIT0 y0)))) (∧ (∀ (λ y0 : El num, (= (+ (BIT1 y0) _0) (BIT1 y0)))) (∧ (∀ (λ y0 : El num, (∀ (λ y1 : El num, (= (+ (BIT0 y0) (BIT0 y1)) (BIT0 (+ y0 y1))))))) (∧ (∀ (λ y0 : El num, (∀ (λ y1 : El num, (= (+ (BIT0 y0) (BIT1 y1)) (BIT1 (+ y0 y1))))))) (∧ (∀ (λ y0 : El num, (∀ (λ y1 : El num, (= (+ (BIT1 y0) (BIT0 y1)) (BIT1 (+ y0 y1))))))) (∀ (λ y0 : El num, (∀ (λ y1 : El num, (= (+ (BIT1 y0) (BIT1 y1)) (BIT0 (SUC (+ y0 y1))))))))))))))));
