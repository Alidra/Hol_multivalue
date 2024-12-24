require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1259314 (d' : El num) (d'' : El num) (p : El num) (q : El num) (m : El num) (n : El num) (d : El num) (h1 : Prf (= m (+ p d'))) (h2 : Prf (= q (+ n d''))) (h3 : Prf (= (+ p q) (+ (+ m n) d))) : Prf (¬ (∃ (λ d''' : El num, (= d (+ (+ d' d'') (SUC d'''))))));
