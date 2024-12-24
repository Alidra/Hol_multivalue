require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1256728 (p : El num) (d'' : El num) (d''' : El num) (n : El num) (d' : El num) : Prf (= (⇒ (= (+ d' (+ d' (SUC d'''))) (NUMERAL _0)) F) (⇒ (= (+ p (+ n d'')) (+ (+ (+ p (+ (+ d' d'') (SUC d'''))) n) d')) F));
