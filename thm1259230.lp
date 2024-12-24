require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1259230_term_abbrevs;
require open hol-light.thm1251285_spec;
require open hol-light.thm1258679_spec;
opaque symbol lem1259230 (d' : El num) (d''' : El num) (n : El num) (d'' : El num) : Prf (term0 d' d''' n d'') ≔ EQ_MP (@lem1251285 d' d''' n d'') (@lem1258679 d''' d');
