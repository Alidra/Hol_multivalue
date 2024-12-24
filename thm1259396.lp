require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1259396_term_abbrevs;
require open hol-light.thm1248678_spec;
require open hol-light.thm1259344_spec;
opaque symbol lem1259396 (d : El num) (m : El num) (d' : El num) (d'' : El num) (h1 : Prf (= (+ m d) (term0 m d' d''))) : Prf (term1 d d' d'') ≔ EQ_MP (@lem1248678 d d' d'') (@lem1259344 d m d' d'' h1);
