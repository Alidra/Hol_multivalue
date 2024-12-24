require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1249859 (d''' : El num) (p : El num) (d'' : El num) (d' : El num) : Prf (= (⇒ (= (SUC d''') (NUMERAL _0)) F) (⇒ (= (+ p (+ (+ d' d'') (SUC d'''))) (+ (+ p d'') d')) F));
