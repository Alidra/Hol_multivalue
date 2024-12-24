require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1252523 (p : El num) (n : El num) (d' : El num) (d'' : El num) (d''' : El num) : Prf (= (⇒ (= (+ d'' (+ d'' (SUC d'''))) (NUMERAL _0)) F) (⇒ (= (+ (+ p d') n) (+ (+ p (+ n d'')) (+ (+ d' d'') (SUC d''')))) F));
