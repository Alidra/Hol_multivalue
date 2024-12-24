require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1259214_term_abbrevs;
require open hol-light.thm1257676_spec;
require open hol-light.thm1259169_spec;
opaque symbol lem1259214 (m : El num) (d''' : El num) (n : El num) (d'' : El num) (d' : El num) : Prf (term0 m d''' n d'' d') ≔ EQ_MP (@lem1257676 m d''' n d'' d') (@lem1259169 d'' d' d''');
