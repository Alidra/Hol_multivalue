require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1259399 (n : El num) (d' : El num) (d : El num) (d'' : El num) (h1 : Prf (= n (+ (+ (+ n d') d) d''))) : Prf (<= d (+ d' d''));
