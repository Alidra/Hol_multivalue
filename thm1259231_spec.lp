require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1259231 (n : El num) (d' : El num) (d''' : El num) (d'' : El num) : Prf (⇒ (= n (+ (+ (+ n d') (+ (+ d' d'') (SUC d'''))) d'')) F);
