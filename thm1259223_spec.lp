require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1259223 (p : El num) (q : El num) (d' : El num) (d'' : El num) (d''' : El num) : Prf (⇒ (= (+ p q) (+ (+ (+ p d') (+ q d'')) (+ (+ d' d'') (SUC d''')))) F);
