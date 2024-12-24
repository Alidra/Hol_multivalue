require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm2299918_term_abbrevs;
require open hol-light.thm2299752_spec;
opaque symbol lem2299918 (n : El num) : Prf (term0 n) ≔ (@lem2299752) n;
