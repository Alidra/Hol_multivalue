require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1247946 (d' : El num) (p : El num) (q : El num) (m : El num) (n : El num) (d : El num) (h1 : Prf (= p (+ m d'))) (h2 : Prf (= (+ p q) (+ (+ m n) d))) : Prf (= (+ (+ m d') q) (+ (+ m n) d));
