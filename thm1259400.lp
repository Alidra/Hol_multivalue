require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1259400_term_abbrevs;
require open hol-light.thm1248614_spec;
require open hol-light.thm1259364_spec;
opaque symbol lem1259400 (p : El num) (d : El num) (d' : El num) (d'' : El num) (h1 : Prf (= p (term0 p d d' d''))) : Prf (term1 d d' d'') ≔ EQ_MP (@lem1248614 d d' d'') (@lem1259364 p d d' d'' h1);
