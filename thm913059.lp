require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm913059_term_abbrevs;
require open hol-light.thm728149_spec;
require open hol-light.thm728158_spec;
opaque symbol lem913059 : Prf (= term0 term1) ≔ TRANS (@lem728149) (@lem728158);
