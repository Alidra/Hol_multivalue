require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1259233_term_abbrevs;
require open hol-light.thm1250376_spec;
require open hol-light.thm1258565_spec;
opaque symbol lem1259233 (d''' : El num) (d' : El num) (p : El num) (d'' : El num) : Prf (term0 d''' d' p d'') ≔ EQ_MP (@lem1250376 d''' d' p d'') (@lem1258565 d''' d');
