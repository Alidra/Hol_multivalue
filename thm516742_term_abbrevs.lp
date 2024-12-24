require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 (x0: El num) ≔ ((λ y0 : El num, (∀ (λ y1 : El num, (∀ (λ y2 : El num, (= (< (* y0 y1) (* y0 y2)) (∧ (¬ (= y0 (NUMERAL _0))) (< y1 y2)))))))) x0);
symbol term2 (x0: El num) (x1: El num) ≔ ((λ y0 : El num, (∀ (λ y1 : El num, (= (< (* x0 y0) (* x0 y1)) (∧ (¬ (= x0 (NUMERAL _0))) (< y0 y1)))))) x1);
symbol term4 (x0: El num) (x1: El num) (x2: El num) ≔ ((λ y0 : El num, (= (< (* x0 x1) (* x0 y0)) (∧ (¬ (= x0 (NUMERAL _0))) (< x1 y0)))) x2);
symbol term1 (x0: El num) ≔ (∀ (λ y0 : El num, (∀ (λ y1 : El num, (= (< (* x0 y0) (* x0 y1)) (∧ (¬ (= x0 (NUMERAL _0))) (< y0 y1)))))));
symbol term3 (x0: El num) (x1: El num) ≔ (∀ (λ y0 : El num, (= (< (* x0 x1) (* x0 y0)) (∧ (¬ (= x0 (NUMERAL _0))) (< x1 y0)))));
