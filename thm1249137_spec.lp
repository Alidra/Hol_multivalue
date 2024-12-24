require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1249137 (d''' : El num) (d' : El num) (m : El num) (d : El num) (d'' : El num) (h1 : Prf (= d (+ (+ d' d'') (SUC d''')))) (h2 : Prf (= (+ m d') (+ (+ m d) d''))) : Prf (= (+ m d') (+ (+ m (+ (+ d' d'') (SUC d'''))) d''));
