require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1249457 (d : El num) (d' : El num) (d'' : El num) (h1 : Prf (∃ (λ d''' : El num, (= d (+ (+ d' d'') (SUC d''')))))) : Prf (∃ (λ d''' : El num, (= d (+ (+ d' d'') (SUC d''')))));
