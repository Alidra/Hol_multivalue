require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1251497 (m : El num) (d' : El num) (d''' : El num) (d'' : El num) : Prf (= (⇒ (= (+ d'' (+ d'' (SUC d'''))) (NUMERAL _0)) F) (⇒ (= (+ m d') (+ (+ m (+ (+ d' d'') (SUC d'''))) d'')) F));
