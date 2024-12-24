require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1248320 (d'' : El num) (q : El num) (p : El num) (d : El num) (n : El num) (d' : El num) (h1 : Prf (= n (+ q d''))) (h2 : Prf (= (+ p q) (+ (+ (+ p d) n) d'))) : Prf (= (+ p q) (+ (+ (+ p d) (+ q d'')) d'));
