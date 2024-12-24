require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1046237 (a : El num) (d : El num) (b : El num) (c : El num) : Prf (= ((λ d' : El num, (= (∧ (¬ (= a b)) (¬ (= c d'))) (¬ (= (+ (* a c) (* b d')) (+ (* a d') (* b c)))))) d) (= (∧ (¬ (= a b)) (¬ (= c d))) (¬ (= (+ (* a c) (* b d)) (+ (* a d) (* b c))))));
