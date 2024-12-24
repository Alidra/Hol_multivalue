require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.DIMINDEX_UNIQUE_term_abbrevs;
require open hol-light.thm7594702_spec;
require open hol-light.thm7598119_spec;
opaque symbol lem7598120 [A] (n : El num) : Prf (term0 A n) ≔ EQ_MP (@lem7594702 A n) (@lem7598119 A n);
