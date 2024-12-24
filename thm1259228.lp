require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1259228_term_abbrevs;
require open hol-light.thm1251719_spec;
require open hol-light.thm1258727_spec;
opaque symbol lem1259228 (d''' : El num) (m : El num) (d' : El num) (d'' : El num) : Prf (term0 d''' m d' d'') ≔ EQ_MP (@lem1251719 d''' m d' d'') (@lem1258727 d''');
