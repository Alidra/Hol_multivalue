require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1259231_term_abbrevs;
require open hol-light.thm1251039_spec;
require open hol-light.thm1258653_spec;
opaque symbol lem1259231 (n : El num) (d' : El num) (d''' : El num) (d'' : El num) : Prf (term0 n d' d''' d'') ≔ EQ_MP (@lem1251039 n d' d''' d'') (@lem1258653 d'' d' d''');
