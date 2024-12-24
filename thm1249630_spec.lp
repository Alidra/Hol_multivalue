require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1249630 (d''' : El num) (d'' : El num) (d : El num) (q : El num) (m : El num) (n : El num) (d' : El num) (h1 : Prf (= d (+ (+ d' d'') (SUC d''')))) (h2 : Prf (= q (+ n d''))) (h3 : Prf (= (+ (+ m d) q) (+ (+ m n) d'))) : Prf (= (+ (+ m (+ (+ d' d'') (SUC d'''))) (+ n d'')) (+ (+ m n) d'));
