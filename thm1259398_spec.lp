require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1259398 (d' : El num) (d : El num) (n : El num) (d'' : El num) (h1 : Prf (= (+ (+ n d') d) (+ n d''))) : Prf (<= d (+ d' d''));
