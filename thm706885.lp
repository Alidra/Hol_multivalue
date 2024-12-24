require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm706885_term_abbrevs;
require open hol-light.thm528081_spec;
require open hol-light.thm528090_spec;
opaque symbol lem706885 : Prf (= term0 term1) ≔ TRANS (@lem528081) (@lem528090);
