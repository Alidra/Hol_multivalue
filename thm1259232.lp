require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1259232_term_abbrevs;
require open hol-light.thm1250723_spec;
require open hol-light.thm1258609_spec;
opaque symbol lem1259232 (p : El num) (d''' : El num) (d' : El num) (d'' : El num) : Prf (term0 p d''' d' d'') ≔ EQ_MP (@lem1250723 p d''' d' d'') (@lem1258609 d'' d' d''');
