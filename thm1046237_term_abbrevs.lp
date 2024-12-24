require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term2 (x0: El num) (x1: El num) (x2: El num) (x3: El num) ≔ (¬ (= (+ (* x0 x3) (* x2 x1)) (+ (* x0 x1) (* x2 x3))));
symbol term0 (x0: El num) (x1: El num) (x2: El num) (x3: El num) ≔ ((λ y0 : El num, (= (∧ (¬ (= x0 x1)) (¬ (= x2 y0))) (¬ (= (+ (* x0 x2) (* x1 y0)) (+ (* x0 y0) (* x1 x2)))))) x3);
symbol term1 (x0: El num) (x1: El num) (x2: El num) (x3: El num) ≔ (∧ (¬ (= x0 x1)) (¬ (= x2 x3)));
