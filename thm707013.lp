require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm707013_term_abbrevs;
require open hol-light.thm534523_spec;
require open hol-light.thm534539_spec;
opaque symbol lem707013 : Prf (= term0 term1) ≔ TRANS (@lem534523) (@lem534539);
