require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1259217 (p : El num) (d''' : El num) (q : El num) (d'' : El num) (d' : El num) : Prf (⇒ (= (+ p q) (+ (+ (+ p (+ (+ d' d'') (SUC d'''))) (+ q d'')) d')) F);
