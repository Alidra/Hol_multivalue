require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1249282 (d''' : El num) (d' : El num) (d'' : El num) (m : El num) (n : El num) (p : El num) (q : El num) (d : El num) (h1 : Prf (= d (+ (+ d' d'') (SUC d''')))) (h2 : Prf (= p (+ m d'))) (h3 : Prf (= q (+ n d''))) (h4 : Prf (= (+ m n) (+ (+ p q) d))) : Prf (= (+ m n) (+ (+ (+ m d') (+ n d'')) (+ (+ d' d'') (SUC d'''))));
