require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1257154 (m : El num) (d'' : El num) (d''' : El num) (q : El num) (d' : El num) : Prf (= (⇒ (= (+ d' (+ d' (SUC d'''))) (NUMERAL _0)) F) (⇒ (= (+ m (+ q d'')) (+ (+ (+ m (+ (+ d' d'') (SUC d'''))) q) d')) F));
