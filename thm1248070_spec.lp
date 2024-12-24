require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1248070 (d'' : El num) (d' : El num) (p : El num) (q : El num) (m : El num) (n : El num) (d : El num) (h1 : Prf (= n (+ q d''))) (h2 : Prf (= p (+ m d'))) (h3 : Prf (= (+ p q) (+ (+ m n) d))) : Prf (= (+ (+ m d') q) (+ (+ m (+ q d'')) d));
