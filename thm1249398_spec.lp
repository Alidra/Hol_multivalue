require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1249398 (d''' : El num) (d' : El num) (d'' : El num) (p : El num) (q : El num) (m : El num) (n : El num) (d : El num) (h1 : Prf (= d (+ (+ d' d'') (SUC d''')))) (h2 : Prf (= p (+ m d'))) (h3 : Prf (= q (+ n d''))) (h4 : Prf (= (+ p q) (+ (+ m n) d))) : Prf (= (+ (+ m d') (+ n d'')) (+ (+ m n) (+ (+ d' d'') (SUC d'''))));
