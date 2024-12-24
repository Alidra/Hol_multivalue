require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.HAS_SIZE_TYBIT1_term_abbrevs;
require open hol-light.thm7932948_spec;
require open hol-light.thm7933086_spec;
opaque symbol lem7933087 [A] : Prf (term0 A) ≔ EQ_MP (@lem7933086 A) (@lem7932948 A);
