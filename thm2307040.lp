require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm2307040_term_abbrevs;
require open hol-light.thm2307039_spec;
opaque symbol lem2307040 : Prf term0 ≔ λ m : El num, (@lem2307039 m);
