require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1247366 (d'' : El num) (p : El num) (d : El num) (n : El num) (d' : El num) (h1 : Prf (= n (+ p d''))) (h2 : Prf (= (+ p d) (+ n d'))) : Prf (= (+ p d) (+ (+ p d'') d'));
