require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1259401_term_abbrevs;
require open hol-light.thm1248598_spec;
require open hol-light.thm1259369_spec;
opaque symbol lem1259401 (d : El num) (d' : El num) (p : El num) (d'' : El num) (h1 : Prf (= (term0 p d d') (+ p d''))) : Prf (term1 d d' d'') ≔ EQ_MP (@lem1248598 d d' d'') (@lem1259369 d d' p d'' h1);
