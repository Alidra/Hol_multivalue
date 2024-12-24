require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1259225_term_abbrevs;
require open hol-light.thm1252920_spec;
require open hol-light.thm1258807_spec;
opaque symbol lem1259225 (m : El num) (q : El num) (d' : El num) (d'' : El num) (d''' : El num) : Prf (term0 m q d' d'' d''') ≔ EQ_MP (@lem1252920 m q d' d'' d''') (@lem1258807 d' d''');
