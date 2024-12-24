require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1247994 (d' : El num) (d'' : El num) (p : El num) (q : El num) (m : El num) (n : El num) (d : El num) (h1 : Prf (= m (+ p d'))) (h2 : Prf (= n (+ q d''))) (h3 : Prf (= (+ p q) (+ (+ m n) d))) : Prf (= (+ p q) (+ (+ (+ p d') (+ q d'')) d));
