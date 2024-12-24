require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem83517 (n : El num) (m : El num) (p : El num) : Prf (∧ (= (* m n) (* n m)) (∧ (= (* (* m n) p) (* m (* n p))) (= (* m (* n p)) (* n (* m p)))));
