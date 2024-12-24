require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm2267742_term_abbrevs;
require open hol-light.thm2267740_spec;
require open hol-light.thm2267741_spec;
opaque symbol lem2267742 (r : El real) : Prf (= (integer r) (= (term0 r) r)) ≔ EQ_MP (@lem2267741 r) (@lem2267740 r);
