require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.FINITE_SUM_IMAGE_term_abbrevs;
require open hol-light.thm7635341_spec;
require open hol-light.thm7637129_spec;
opaque symbol lem7637130 [A B] : Prf (= (@UNIV (finite_sum A B)) (term0 A B)) ≔ EQ_MP (@lem7635341 A B) (@lem7637129 A B);
