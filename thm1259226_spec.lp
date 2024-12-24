require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1259226 (p : El num) (n : El num) (d' : El num) (d'' : El num) (d''' : El num) : Prf (⇒ (= (+ (+ p d') n) (+ (+ p (+ n d'')) (+ (+ d' d'') (SUC d''')))) F);
