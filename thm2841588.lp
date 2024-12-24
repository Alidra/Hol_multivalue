require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm2841588_term_abbrevs;
require open hol-light.int_neg_th_spec;
opaque symbol lem2841588 (x : El int) : Prf (term0 x) ≔ (@lem2273074) x;
