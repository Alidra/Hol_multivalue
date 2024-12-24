require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem522116 (n : El num) (m : El num) (p : El num) : Prf ((λ p' : El num, (= (* m (+ n p')) (+ (* m n) (* m p')))) p);
