require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.ONE_term_abbrevs;
require open hol-light.thm0_spec;
require open hol-light.thm80360_spec;
opaque symbol lem80361 : Prf (= term0 term1) ≔ EQ_MP (@lem80360) (@lem0);
