require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1257676 (m : El num) (d''' : El num) (n : El num) (d'' : El num) (d' : El num) : Prf (= (⇒ (= (+ d'' (+ d'' (+ d' (+ d' (SUC d'''))))) (NUMERAL _0)) F) (⇒ (= (+ m n) (+ (+ (+ m (+ (+ d' d'') (SUC d'''))) (+ n d'')) d')) F));
