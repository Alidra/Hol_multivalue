require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1249485 (d''' : El num) (d'' : El num) (q : El num) (p : El num) (d : El num) (n : El num) (d' : El num) (h1 : Prf (= d (+ (+ d' d'') (SUC d''')))) (h2 : Prf (= n (+ q d''))) (h3 : Prf (= (+ p q) (+ (+ (+ p d) n) d'))) : Prf (= (+ p q) (+ (+ (+ p (+ (+ d' d'') (SUC d'''))) (+ q d'')) d'));
