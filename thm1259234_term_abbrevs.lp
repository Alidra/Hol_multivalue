require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 (x0: El num) (x1: El num) (x2: El num) (x3: El num) ≔ (⇒ (= (+ (+ x2 x0) (+ (+ x3 x0) (SUC x1))) (+ x2 x3)) F);
