require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1259216_term_abbrevs;
require open hol-light.thm1256728_spec;
require open hol-light.thm1259093_spec;
opaque symbol lem1259216 (p : El num) (d'' : El num) (d''' : El num) (n : El num) (d' : El num) : Prf (term0 p d'' d''' n d') ≔ EQ_MP (@lem1256728 p d'' d''' n d') (@lem1259093 d' d''');
