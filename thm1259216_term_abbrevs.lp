require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 (x0: El num) (x1: El num) (x2: El num) (x3: El num) (x4: El num) ≔ (⇒ (= (+ x0 (+ x3 x1)) (+ (+ (+ x0 (+ (+ x4 x1) (SUC x2))) x3) x4)) F);
