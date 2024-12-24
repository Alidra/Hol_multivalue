require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem513551 (n : El num) (m : El num) (p : El num) : Prf (∧ (= (+ (+ m n) p) (+ m (+ n p))) (= (+ m (+ n p)) (+ n (+ m p))));
