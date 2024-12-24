require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1259215_term_abbrevs;
require open hol-light.thm1257154_spec;
require open hol-light.thm1259125_spec;
opaque symbol lem1259215 (m : El num) (d'' : El num) (d''' : El num) (q : El num) (d' : El num) : Prf (term0 m d'' d''' q d') ≔ EQ_MP (@lem1257154 m d'' d''' q d') (@lem1259125 d' d''');
