require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.RAT_LEMMA5_term_abbrevs;
require open hol-light.thm1979880_spec;
opaque symbol lem1979881 (x1 : El real) (y2 : El real) (x2 : El real) (y1 : El real) : Prf (term0 x1 y2 x2 y1) ≔ λ h0 : Prf (term1 y1 y2), (@lem1979880 x1 x2 y1 y2 h0);
