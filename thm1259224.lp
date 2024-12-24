require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1259224_term_abbrevs;
require open hol-light.thm1253393_spec;
require open hol-light.thm1258851_spec;
opaque symbol lem1259224 (m : El num) (n : El num) (d' : El num) (d'' : El num) (d''' : El num) : Prf (term0 m n d' d'' d''') ≔ EQ_MP (@lem1253393 m n d' d'' d''') (@lem1258851 d'' d' d''');
