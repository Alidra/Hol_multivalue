require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1259219_term_abbrevs;
require open hol-light.thm1255398_spec;
require open hol-light.thm1259001_spec;
opaque symbol lem1259219 (d''' : El num) (d'' : El num) (p : El num) (q : El num) (d' : El num) : Prf (term0 d''' d'' p q d') ≔ EQ_MP (@lem1255398 d''' d'' p q d') (@lem1259001 d''' d'');
