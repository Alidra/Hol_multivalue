require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1259216 (p : El num) (d'' : El num) (d''' : El num) (n : El num) (d' : El num) : Prf (⇒ (= (+ p (+ n d'')) (+ (+ (+ p (+ (+ d' d'') (SUC d'''))) n) d')) F);
