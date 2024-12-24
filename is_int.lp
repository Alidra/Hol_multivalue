require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.is_int_term_abbrevs;
require open hol-light.thm2259383_spec;
require open hol-light.thm2267613_spec;
opaque symbol lem2267614 (x : El real) : Prf (= (integer x) (term0 x)) ≔ EQ_MP (@lem2259383 x) (@lem2267613 x);
