require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term3 (x0: El num) (x1: El num) ≔ ((λ y0 : El num, (= (- x0 (SUC y0)) (PRE (- x0 y0)))) x1);
symbol term2 (x0: El num) ≔ (∀ (λ y0 : El num, (= (- x0 (SUC y0)) (PRE (- x0 y0)))));
symbol term0 ≔ (∀ (λ y0 : El num, (∀ (λ y1 : El num, (= (- y0 (SUC y1)) (PRE (- y0 y1)))))));
symbol term1 (x0: El num) ≔ ((λ y0 : El num, (∀ (λ y1 : El num, (= (- y0 (SUC y1)) (PRE (- y0 y1)))))) x0);
