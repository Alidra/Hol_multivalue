require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm706951_term_abbrevs;
require open hol-light.thm531233_spec;
require open hol-light.thm531248_spec;
opaque symbol lem706951 : Prf (= term0 term1) ≔ TRANS (@lem531233) (@lem531248);
