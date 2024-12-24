require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1249427 (d''' : El num) (d'' : El num) (d : El num) (n : El num) (p : El num) (q : El num) (d' : El num) (h1 : Prf (= d (+ (+ d' d'') (SUC d''')))) (h2 : Prf (= n (+ q d''))) (h3 : Prf (= (+ (+ p d) n) (+ (+ p q) d'))) : Prf (= (+ (+ p (+ (+ d' d'') (SUC d'''))) (+ q d'')) (+ (+ p q) d'));
