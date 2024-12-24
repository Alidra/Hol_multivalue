require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1259284 (d'' : El num) (q : El num) (p : El num) (d : El num) (n : El num) (d' : El num) (h1 : Prf (= q (+ n d''))) (h2 : Prf (= (+ p q) (+ (+ (+ p d) n) d'))) : Prf (¬ (∃ (λ d''' : El num, (= d (+ (+ d' d'') (SUC d'''))))));
