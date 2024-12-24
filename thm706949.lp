require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm706949_term_abbrevs;
require open hol-light.thm531147_spec;
require open hol-light.thm531152_spec;
opaque symbol lem706949 : Prf (= term0 term1) ≔ TRANS (@lem531147) (@lem531152);
