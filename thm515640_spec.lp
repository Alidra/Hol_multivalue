require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem515640 (n : El num) (m : El num) (p : El num) : Prf ((λ p' : El num, (= (EXP m (+ n p')) (* (EXP m n) (EXP m p')))) p);
