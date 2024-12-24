require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1259227_term_abbrevs;
require open hol-light.thm1252107_spec;
require open hol-light.thm1258743_spec;
opaque symbol lem1259227 (p : El num) (q : El num) (d' : El num) (d'' : El num) (d''' : El num) : Prf (term0 p q d' d'' d''') ≔ EQ_MP (@lem1252107 p q d' d'' d''') (@lem1258743 d''');
