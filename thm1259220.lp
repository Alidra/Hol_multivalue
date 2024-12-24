require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1259220_term_abbrevs;
require open hol-light.thm1254983_spec;
require open hol-light.thm1258975_spec;
opaque symbol lem1259220 (m : El num) (n : El num) (d' : El num) (d'' : El num) (d''' : El num) : Prf (term0 m n d' d'' d''') ≔ EQ_MP (@lem1254983 m n d' d'' d''') (@lem1258975 d''');
