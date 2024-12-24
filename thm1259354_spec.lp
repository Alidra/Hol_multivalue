require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1259354 (d' : El num) (d : El num) (n : El num) (d'' : El num) (h1 : Prf (= (+ (+ n d') d) (+ n d''))) : Prf (¬ (∃ (λ d''' : El num, (= d (+ (+ d' d'') (SUC d'''))))));
