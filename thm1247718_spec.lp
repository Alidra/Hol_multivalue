require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1247718 (d' : El num) (m : El num) (n : El num) (p : El num) (q : El num) (d : El num) (h1 : Prf (= p (+ m d'))) (h2 : Prf (= (+ m n) (+ (+ p q) d))) : Prf (= (+ m n) (+ (+ (+ m d') q) d));
