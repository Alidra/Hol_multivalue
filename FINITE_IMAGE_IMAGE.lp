require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.FINITE_IMAGE_IMAGE_term_abbrevs;
require open hol-light.thm7603578_spec;
require open hol-light.thm7604549_spec;
opaque symbol lem7604550 [A] : Prf (= (@UNIV (finite_image A)) (term0 A)) ≔ EQ_MP (@lem7603578 A) (@lem7604549 A);
