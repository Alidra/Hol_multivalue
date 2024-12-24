require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1251039 (n : El num) (d' : El num) (d''' : El num) (d'' : El num) : Prf (= (⇒ (= (+ d'' (+ d'' (+ d' (+ d' (SUC d'''))))) (NUMERAL _0)) F) (⇒ (= n (+ (+ (+ n d') (+ (+ d' d'') (SUC d'''))) d'')) F));
