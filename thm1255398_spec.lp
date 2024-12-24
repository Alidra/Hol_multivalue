require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1255398 (d''' : El num) (d'' : El num) (p : El num) (q : El num) (d' : El num) : Prf (= (⇒ (= (+ (SUC d''') (+ d'' d'')) (NUMERAL _0)) F) (⇒ (= (+ (+ p (+ (+ d' d'') (SUC d'''))) (+ q d'')) (+ (+ p q) d')) F));
