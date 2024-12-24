require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1259219 (d''' : El num) (d'' : El num) (p : El num) (q : El num) (d' : El num) : Prf (⇒ (= (+ (+ p (+ (+ d' d'') (SUC d'''))) (+ q d'')) (+ (+ p q) d')) F);
