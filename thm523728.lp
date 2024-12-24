require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm523728_term_abbrevs;
require open hol-light.thm523717_spec;
opaque symbol lem523728 (n : El num) : Prf (term0 n) ≔ (@lem523717) n;
