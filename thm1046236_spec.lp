require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1046236 (a : El num) (b : El num) (c : El num) (d : El num) : Prf ((λ d' : El num, (= (∧ (¬ (= a b)) (¬ (= c d'))) (¬ (= (+ (* a c) (* b d')) (+ (* a d') (* b c)))))) d);
