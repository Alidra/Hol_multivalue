require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm912741_term_abbrevs;
require open hol-light.thm709031_spec;
require open hol-light.thm709039_spec;
opaque symbol lem912741 : Prf (= term0 term1) ≔ TRANS (@lem709031) (@lem709039);
