require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1247478 (d : El num) (m : El num) (n : El num) (d' : El num) (h1 : Prf (= m (+ n d'))) : Prf (= (<= d (+ d' (dist ((@̦‚ num num) n (+ (+ n d') d))))) (<= d (+ d' (dist ((@̦‚ num num) n (+ m d))))));
