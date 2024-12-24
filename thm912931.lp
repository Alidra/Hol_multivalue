require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm912931_term_abbrevs;
require open hol-light.thm719529_spec;
require open hol-light.thm719543_spec;
opaque symbol lem912931 : Prf (= term0 term1) ≔ TRANS (@lem719529) (@lem719543);
