require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 (x0: El num) (x1: El num) (x2: El num) (x3: El num) (x4: El num) (x5: El num) (x6: El num) (x7: El num) ≔ (∧ (= (+ x0 (+ x1 x2)) (+ (+ x0 x1) x2)) (∧ (= (* (EXP x6 x3) (EXP x6 x7)) (EXP x6 (+ x3 x7))) (∧ (= (* x6 (EXP x6 x7)) (EXP x6 (SUC x7))) (∧ (= (* (EXP x6 x7) x6) (EXP x6 (SUC x7))) (∧ (= (* x6 x6) (EXP x6 (NUMERAL (BIT0 (BIT1 _0))))) (∧ (= (EXP (* x6 x4) x7) (* (EXP x6 x7) (EXP x4 x7))) (∧ (= (EXP (EXP x6 x3) x7) (EXP x6 (* x3 x7))) (∧ (= (EXP x6 (NUMERAL _0)) (NUMERAL (BIT1 _0))) (∧ (= (EXP x6 (NUMERAL (BIT1 _0))) x6) (∧ (= (* x6 (+ x4 x5)) (+ (* x6 x4) (* x6 x5))) (= (EXP x6 (SUC x7)) (* x6 (EXP x6 x7)))))))))))));
