require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1254597 (m : El num) (q : El num) (d' : El num) (d'' : El num) (d''' : El num) : Prf (= (⇒ (= (+ d'' (+ d'' (SUC d'''))) (NUMERAL _0)) F) (⇒ (= (+ (+ m d') q) (+ (+ m (+ q d'')) (+ (+ d' d'') (SUC d''')))) F));
