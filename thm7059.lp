require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm7059_term_abbrevs;
require open hol-light.thm7058_spec;
opaque symbol lem7059 (A : El bool) (C : El bool) (B : El bool) (D : El bool) : Prf (term0 A C B D) ≔ λ h0 : Prf (term1 A B C D), (@lem7058 A B C D h0);
