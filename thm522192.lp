require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm522192_term_abbrevs;
require open hol-light.thm522176_spec;
opaque symbol lem522192 (n : El num) : Prf (term0 n) ≔ (@lem522176) n;
