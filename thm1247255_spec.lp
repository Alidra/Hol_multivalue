require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1247255 (n : El num) (m : El num) (p : El num) (d : El num) (h1 : Prf (= m (+ p d))) : Prf (= (<= d (+ (dist ((@̦‚ num num) (+ p d) n)) (dist ((@̦‚ num num) n p)))) (<= d (+ (dist ((@̦‚ num num) m n)) (dist ((@̦‚ num num) n p)))));
