require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1259369 (d : El num) (d' : El num) (p : El num) (d'' : El num) (h1 : Prf (= (+ (+ p d) d') (+ p d''))) : Prf (¬ (∃ (λ d''' : El num, (= d (+ (+ d' d'') (SUC d'''))))));
