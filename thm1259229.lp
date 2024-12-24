require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1259229_term_abbrevs;
require open hol-light.thm1251497_spec;
require open hol-light.thm1258711_spec;
opaque symbol lem1259229 (m : El num) (d' : El num) (d''' : El num) (d'' : El num) : Prf (term0 m d' d''' d'') ≔ EQ_MP (@lem1251497 m d' d''' d'') (@lem1258711 d'' d''');
