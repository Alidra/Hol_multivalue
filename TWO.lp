require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.TWO_term_abbrevs;
require open hol-light.thm0_spec;
require open hol-light.thm80550_spec;
opaque symbol lem80551 : Prf (= term0 term1) ≔ EQ_MP (@lem80550) (@lem0);
