require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm516565_term_abbrevs;
require open hol-light.thm75543_spec;
opaque symbol lem516565 (n : El num) : Prf (term0 n) ≔ (@lem75543) n;
