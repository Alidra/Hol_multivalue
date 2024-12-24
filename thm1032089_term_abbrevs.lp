require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 (x0: El num) (x1: El num) (x2: El num) (x3: El num) (x4: El num) (x5: El num) (x6: El num) (x7: El num) (x8: El num) ≔ (∧ (= (+ (+ x1 x0) x2) (+ x1 (+ x0 x2))) (∧ (= (+ x1 (+ x2 x3)) (+ x2 (+ x1 x3))) (∧ (= (+ (+ x1 x0) x2) (+ (+ x1 x2) x0)) (∧ (= (+ x1 x2) (+ x2 x1)) (∧ (= (+ x1 (+ x2 x3)) (+ (+ x1 x2) x3)) (∧ (= (* (EXP x7 x4) (EXP x7 x8)) (EXP x7 (+ x4 x8))) (∧ (= (* x7 (EXP x7 x8)) (EXP x7 (SUC x8))) (∧ (= (* (EXP x7 x8) x7) (EXP x7 (SUC x8))) (∧ (= (* x7 x7) (EXP x7 (NUMERAL (BIT0 (BIT1 _0))))) (∧ (= (EXP (* x7 x5) x8) (* (EXP x7 x8) (EXP x5 x8))) (∧ (= (EXP (EXP x7 x4) x8) (EXP x7 (* x4 x8))) (∧ (= (EXP x7 (NUMERAL _0)) (NUMERAL (BIT1 _0))) (∧ (= (EXP x7 (NUMERAL (BIT1 _0))) x7) (∧ (= (* x7 (+ x5 x6)) (+ (* x7 x5) (* x7 x6))) (= (EXP x7 (SUC x8)) (* x7 (EXP x7 x8)))))))))))))))));
