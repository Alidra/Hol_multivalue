require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm912803_term_abbrevs;
require open hol-light.thm712018_spec;
require open hol-light.thm712026_spec;
opaque symbol lem912803 : Prf (= term0 term1) ≔ TRANS (@lem712018) (@lem712026);
