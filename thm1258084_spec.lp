require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1258084 (d''' : El num) (m : El num) (q : El num) (d'' : El num) (d' : El num) : Prf (= (⇒ (= (SUC d''') (NUMERAL _0)) F) (⇒ (= (+ (+ m (+ (+ d' d'') (SUC d'''))) q) (+ (+ m (+ q d'')) d')) F));
