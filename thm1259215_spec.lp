require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1259215 (m : El num) (d'' : El num) (d''' : El num) (q : El num) (d' : El num) : Prf (⇒ (= (+ m (+ q d'')) (+ (+ (+ m (+ (+ d' d'') (SUC d'''))) q) d')) F);
