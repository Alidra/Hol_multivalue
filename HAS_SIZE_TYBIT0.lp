require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.HAS_SIZE_TYBIT0_term_abbrevs;
require open hol-light.thm7932146_spec;
require open hol-light.thm7932263_spec;
opaque symbol lem7932264 [A] : Prf (term0 A) ≔ EQ_MP (@lem7932263 A) (@lem7932146 A);
