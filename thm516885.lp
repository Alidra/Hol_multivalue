require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm516885_term_abbrevs;
require open hol-light.thm516863_spec;
opaque symbol lem516885 (n : El num) : Prf (term0 n) ≔ (@lem516863) n;
