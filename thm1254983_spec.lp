require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1254983 (m : El num) (n : El num) (d' : El num) (d'' : El num) (d''' : El num) : Prf (= (⇒ (= (SUC d''') (NUMERAL _0)) F) (⇒ (= (+ (+ m d') (+ n d'')) (+ (+ m n) (+ (+ d' d'') (SUC d''')))) F));
