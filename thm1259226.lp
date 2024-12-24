require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1259226_term_abbrevs;
require open hol-light.thm1252523_spec;
require open hol-light.thm1258775_spec;
opaque symbol lem1259226 (p : El num) (n : El num) (d' : El num) (d'' : El num) (d''' : El num) : Prf (term0 p n d' d'' d''') ≔ EQ_MP (@lem1252523 p n d' d'' d''') (@lem1258775 d'' d''');
