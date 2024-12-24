require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1247318 (n : El num) (p : El num) (d : El num) (d' : El num) (h1 : Prf (= n (+ (+ p d) d'))) : Prf (= (<= d (+ d' (dist ((@̦‚ num num) (+ (+ p d) d') p)))) (<= d (+ d' (dist ((@̦‚ num num) n p)))));
