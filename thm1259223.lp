require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1259223_term_abbrevs;
require open hol-light.thm1253868_spec;
require open hol-light.thm1258895_spec;
opaque symbol lem1259223 (p : El num) (q : El num) (d' : El num) (d'' : El num) (d''' : El num) : Prf (term0 p q d' d'' d''') ≔ EQ_MP (@lem1253868 p q d' d'' d''') (@lem1258895 d'' d' d''');
