require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1259397_term_abbrevs;
require open hol-light.thm1248662_spec;
require open hol-light.thm1259349_spec;
opaque symbol lem1259397 (d' : El num) (m : El num) (d : El num) (d'' : El num) (h1 : Prf (= (+ m d') (term0 m d d''))) : Prf (term1 d d' d'') ≔ EQ_MP (@lem1248662 d d' d'') (@lem1259349 d' m d d'' h1);
