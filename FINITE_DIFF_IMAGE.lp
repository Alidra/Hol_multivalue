require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.FINITE_DIFF_IMAGE_term_abbrevs;
require open hol-light.thm7673122_spec;
require open hol-light.thm7689527_spec;
opaque symbol lem7689528 [A B] : Prf (= (@UNIV (finite_diff A B)) (term0 A B)) ≔ EQ_MP (@lem7673122 A B) (@lem7689527 A B);
