require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm706947_term_abbrevs;
require open hol-light.thm531066_spec;
opaque symbol lem706947 : Prf (= term0 term1) ≔ (@lem531066 (BIT1 _0));
