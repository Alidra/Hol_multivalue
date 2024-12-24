require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1248446 (d'' : El num) (n : El num) (m : El num) (d : El num) (q : El num) (d' : El num) (h1 : Prf (= n (+ q d''))) (h2 : Prf (= (+ m n) (+ (+ (+ m d) q) d'))) : Prf (= (+ m (+ q d'')) (+ (+ (+ m d) q) d'));
