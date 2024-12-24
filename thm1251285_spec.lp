require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1251285 (d' : El num) (d''' : El num) (n : El num) (d'' : El num) : Prf (= (⇒ (= (+ (SUC d''') (+ d' d')) (NUMERAL _0)) F) (⇒ (= (+ (+ n d') (+ (+ d' d'') (SUC d'''))) (+ n d'')) F));
