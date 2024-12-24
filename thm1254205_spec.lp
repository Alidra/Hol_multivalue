require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1254205 (p : El num) (n : El num) (d' : El num) (d'' : El num) (d''' : El num) : Prf (= (⇒ (= (+ d' (+ d' (SUC d'''))) (NUMERAL _0)) F) (⇒ (= (+ p (+ n d'')) (+ (+ (+ p d') n) (+ (+ d' d'') (SUC d''')))) F));
