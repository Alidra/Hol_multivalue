require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1259213_term_abbrevs;
require open hol-light.thm1258084_spec;
require open hol-light.thm1259185_spec;
opaque symbol lem1259213 (d''' : El num) (m : El num) (q : El num) (d'' : El num) (d' : El num) : Prf (term0 d''' m q d'' d') ≔ EQ_MP (@lem1258084 d''' m q d'' d') (@lem1259185 d''');
