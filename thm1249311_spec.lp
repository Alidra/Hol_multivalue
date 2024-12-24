require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1249311 (d''' : El num) (d' : El num) (d'' : El num) (p : El num) (q : El num) (m : El num) (n : El num) (d : El num) (h1 : Prf (= d (+ (+ d' d'') (SUC d''')))) (h2 : Prf (= m (+ p d'))) (h3 : Prf (= n (+ q d''))) (h4 : Prf (= (+ p q) (+ (+ m n) d))) : Prf (= (+ p q) (+ (+ (+ p d') (+ q d'')) (+ (+ d' d'') (SUC d'''))));
