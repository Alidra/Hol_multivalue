require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm7250_term_abbrevs;
require open hol-light.thm7249_spec;
opaque symbol lem7250 (A : El bool) (C : El bool) (B : El bool) (D : El bool) : Prf (term0 A C B D) ≔ λ h0 : Prf (term1 B A C D), (@lem7249 B A C D h0);
