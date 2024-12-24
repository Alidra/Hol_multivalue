require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1248146 (n : El num) (q : El num) (p : El num) (m : El num) (d : El num) (h1 : Prf (= p (+ m d))) : Prf (= (<= d (+ (dist ((@̦‚ num num) (+ m n) (+ (+ m d) q))) (dist ((@̦‚ num num) n q)))) (<= d (+ (dist ((@̦‚ num num) (+ m n) (+ p q))) (dist ((@̦‚ num num) n q)))));
