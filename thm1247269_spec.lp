require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1247269 (n : El num) (p : El num) (m : El num) (d : El num) (h1 : Prf (= p (+ m d))) : Prf (= (<= d (+ (dist ((@̦‚ num num) m n)) (dist ((@̦‚ num num) n (+ m d))))) (<= d (+ (dist ((@̦‚ num num) m n)) (dist ((@̦‚ num num) n p)))));
