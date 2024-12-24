require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm71261_term_abbrevs;
opaque symbol lem71261 (r : El ind) : Prf (= (NUM_REP r) (= (term0 r) r)) ≔ @axiom_8 r;
