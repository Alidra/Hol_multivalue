require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.RAT_LEMMA3_term_abbrevs;
require open hol-light.thm1978411_spec;
opaque symbol lem1978412 (x1 : El real) (x2 : El real) (y1 : El real) (y2 : El real) : Prf (term0 x1 x2 y1 y2) ≔ λ h0 : Prf (term1 y1 y2), (@lem1978411 x1 x2 y1 y2 h0);
