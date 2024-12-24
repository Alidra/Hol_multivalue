require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem302578 (p : El num) (m : El num) (n : El num) : Prf (= ((λ p' : El num, (= (= (+ m p') (+ n p')) (= m n))) p) (= (= (+ m p) (+ n p)) (= m n)));
