require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1259217_term_abbrevs;
require open hol-light.thm1256354_spec;
require open hol-light.thm1259061_spec;
opaque symbol lem1259217 (p : El num) (d''' : El num) (q : El num) (d'' : El num) (d' : El num) : Prf (term0 p d''' q d'' d') ≔ EQ_MP (@lem1256354 p d''' q d'' d') (@lem1259061 d'' d' d''');
