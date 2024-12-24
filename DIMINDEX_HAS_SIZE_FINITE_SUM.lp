require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.DIMINDEX_HAS_SIZE_FINITE_SUM_term_abbrevs;
require open hol-light.thm7637206_spec;
require open hol-light.thm7640378_spec;
opaque symbol lem7640379 [M N] : Prf (term0 M N) ≔ EQ_MP (@lem7637206 M N) (@lem7640378 M N);
