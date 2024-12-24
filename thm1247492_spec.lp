require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1247492 (d : El num) (n : El num) (m : El num) (d' : El num) (h1 : Prf (= n (+ m d'))) : Prf (= (<= d (+ d' (dist ((@̦‚ num num) (+ m d') (+ m d))))) (<= d (+ d' (dist ((@̦‚ num num) n (+ m d))))));
