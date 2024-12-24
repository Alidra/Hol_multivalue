require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1249195 (d''' : El num) (d' : El num) (d'' : El num) (m : El num) (n : El num) (p : El num) (q : El num) (d : El num) (h1 : Prf (= d (+ (+ d' d'') (SUC d''')))) (h2 : Prf (= m (+ p d'))) (h3 : Prf (= n (+ q d''))) (h4 : Prf (= (+ m n) (+ (+ p q) d))) : Prf (= (+ (+ p d') (+ q d'')) (+ (+ p q) (+ (+ d' d'') (SUC d'''))));
