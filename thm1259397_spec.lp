require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1259397 (d' : El num) (m : El num) (d : El num) (d'' : El num) (h1 : Prf (= (+ m d') (+ (+ m d) d''))) : Prf (<= d (+ d' d''));
