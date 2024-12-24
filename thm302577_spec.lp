require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem302577 (m : El num) (n : El num) (p : El num) : Prf ((λ p' : El num, (= (= (+ m p') (+ n p')) (= m n))) p);
