require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1249283_term_abbrevs;
opaque symbol lem1249283 (d : El num) (d' : El num) (d'' : El num) (h1 : Prf (term0 d d' d'')) : Prf (term0 d d' d'') ≔ h1;
