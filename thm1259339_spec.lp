require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1259339 (d' : El num) (d'' : El num) (m : El num) (n : El num) (p : El num) (q : El num) (d : El num) (h1 : Prf (= m (+ p d'))) (h2 : Prf (= n (+ q d''))) (h3 : Prf (= (+ m n) (+ (+ p q) d))) : Prf (¬ (∃ (λ d''' : El num, (= d (+ (+ d' d'') (SUC d'''))))));
