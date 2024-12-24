require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm9120_term_abbrevs;
private symbol lem9114 (p : El bool) (h1 : Prf p) : Prf p ≔ h1;
opaque symbol lem9115 (p : El bool) : Prf (⇒ p p) ≔ λ h0 : Prf p, (@lem9114 p h0);
opaque symbol lem9120 : Prf term0 ≔ λ p : El bool, (@lem9115 p);
