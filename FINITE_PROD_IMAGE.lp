require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.FINITE_PROD_IMAGE_term_abbrevs;
require open hol-light.thm7919719_spec;
require open hol-light.thm7921507_spec;
opaque symbol lem7921508 [A B] : Prf (= (@UNIV (finite_prod A B)) (term0 A B)) ≔ EQ_MP (@lem7919719 A B) (@lem7921507 A B);
