require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1259218_term_abbrevs;
require open hol-light.thm1255830_spec;
require open hol-light.thm1259017_spec;
opaque symbol lem1259218 (d''' : El num) (p : El num) (n : El num) (d'' : El num) (d' : El num) : Prf (term0 d''' p n d'' d') ≔ EQ_MP (@lem1255830 d''' p n d'' d') (@lem1259017 d''');
