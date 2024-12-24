require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1249108 (d''' : El num) (d' : El num) (d : El num) (n : El num) (d'' : El num) (h1 : Prf (= d (+ (+ d' d'') (SUC d''')))) (h2 : Prf (= (+ (+ n d') d) (+ n d''))) : Prf (= (+ (+ n d') (+ (+ d' d'') (SUC d'''))) (+ n d''));
