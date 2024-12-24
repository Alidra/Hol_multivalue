require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1259221 (m : El num) (q : El num) (d' : El num) (d'' : El num) (d''' : El num) : Prf (⇒ (= (+ (+ m d') q) (+ (+ m (+ q d'')) (+ (+ d' d'') (SUC d''')))) F);
