require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1259235_term_abbrevs;
require open hol-light.thm1249859_spec;
require open hol-light.thm1258513_spec;
opaque symbol lem1259235 (d''' : El num) (p : El num) (d'' : El num) (d' : El num) : Prf (term0 d''' p d'' d') ≔ EQ_MP (@lem1249859 d''' p d'' d') (@lem1258513 d''');
