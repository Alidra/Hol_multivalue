require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm913187_term_abbrevs;
require open hol-light.thm737721_spec;
require open hol-light.thm737741_spec;
opaque symbol lem913187 : Prf (= term0 term1) ≔ TRANS (@lem737721) (@lem737741);
