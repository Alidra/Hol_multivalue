require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem522102 (m : El num) (n : El num) (p : El num) : Prf (= ((λ p' : El num, (= (+ (+ m n) p') (+ m (+ n p')))) p) (= (+ (+ m n) p) (+ m (+ n p))));
