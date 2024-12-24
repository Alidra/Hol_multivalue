require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1249021 (d''' : El num) (d : El num) (d' : El num) (p : El num) (d'' : El num) (h1 : Prf (= d (+ (+ d' d'') (SUC d''')))) (h2 : Prf (= (+ (+ p d) d') (+ p d''))) : Prf (= (+ (+ p (+ (+ d' d'') (SUC d'''))) d') (+ p d''));
