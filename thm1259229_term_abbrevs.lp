require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 (x0: El num) (x1: El num) (x2: El num) (x3: El num) ≔ (⇒ (= (+ x0 x1) (+ (+ x0 (+ (+ x1 x3) (SUC x2))) x3)) F);
