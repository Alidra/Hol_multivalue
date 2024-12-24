require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm2267740_term_abbrevs;
require open hol-light.thm2267735_spec;
opaque symbol lem2267739 : Prf term0 ≔ λ r : El real, (@lem2267735 r);
opaque symbol lem2267740 (r : El real) : Prf (term1 r) ≔ (@lem2267739) r;
