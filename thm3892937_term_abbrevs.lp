require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 (x0: El a0) (x1: El a0) (x2: El (fun a0 bool)) (x3: El bool) ≔ (∧ (= (∧ (¬ ((@IN a0) x1 ((@INSERT a0) x0 (@EMPTY a0)))) x3) (∧ (¬ (= x1 x0)) x3)) (= (∧ (¬ ((@IN a0) x1 ((@INSERT a0) x0 x2))) x3) (∧ (¬ (= x1 x0)) (∧ (¬ ((@IN a0) x1 x2)) x3))));
