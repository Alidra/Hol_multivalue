require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1259229 (m : El num) (d' : El num) (d''' : El num) (d'' : El num) : Prf (⇒ (= (+ m d') (+ (+ m (+ (+ d' d'') (SUC d'''))) d'')) F);
