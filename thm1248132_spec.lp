require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1248132 (n : El num) (q : El num) (m : El num) (p : El num) (d : El num) (h1 : Prf (= m (+ p d))) : Prf (= (<= d (+ (dist ((@̦‚ num num) (+ (+ p d) n) (+ p q))) (dist ((@̦‚ num num) n q)))) (<= d (+ (dist ((@̦‚ num num) (+ m n) (+ p q))) (dist ((@̦‚ num num) n q)))));
