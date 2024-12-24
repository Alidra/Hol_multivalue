require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1249514 (d''' : El num) (d'' : El num) (q : El num) (p : El num) (d : El num) (n : El num) (d' : El num) (h1 : Prf (= d (+ (+ d' d'') (SUC d''')))) (h2 : Prf (= q (+ n d''))) (h3 : Prf (= (+ p q) (+ (+ (+ p d) n) d'))) : Prf (= (+ p (+ n d'')) (+ (+ (+ p (+ (+ d' d'') (SUC d'''))) n) d'));
