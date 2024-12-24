require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1252107 (p : El num) (q : El num) (d' : El num) (d'' : El num) (d''' : El num) : Prf (= (⇒ (= (SUC d''') (NUMERAL _0)) F) (⇒ (= (+ (+ p d') (+ q d'')) (+ (+ p q) (+ (+ d' d'') (SUC d''')))) F));
