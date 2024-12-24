require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1259399_term_abbrevs;
require open hol-light.thm1248630_spec;
require open hol-light.thm1259359_spec;
opaque symbol lem1259399 (n : El num) (d' : El num) (d : El num) (d'' : El num) (h1 : Prf (= n (term0 n d' d d''))) : Prf (term1 d d' d'') ≔ EQ_MP (@lem1248630 d d' d'') (@lem1259359 n d' d d'' h1);
