require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm706889_term_abbrevs;
require open hol-light.thm528257_spec;
require open hol-light.thm528273_spec;
opaque symbol lem706889 : Prf (= term0 term1) ≔ TRANS (@lem528257) (@lem528273);
