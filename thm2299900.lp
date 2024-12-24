require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm2299900_term_abbrevs;
require open hol-light.thm2299800_spec;
opaque symbol lem2299900 (x : El int) : Prf (term0 x) ≔ (@lem2299800) x;
