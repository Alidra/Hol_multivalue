require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1248992 (d''' : El num) (d'' : El num) (p : El num) (d : El num) (n : El num) (d' : El num) (h1 : Prf (= d (+ (+ d' d'') (SUC d''')))) (h2 : Prf (= p (+ n d''))) (h3 : Prf (= (+ p d) (+ n d'))) : Prf (= (+ (+ n d'') (+ (+ d' d'') (SUC d'''))) (+ n d'));
