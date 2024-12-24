require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm3184729_term_abbrevs;
require open hol-light.thm3184696_spec;
opaque symbol lem3184724 [_83123] (P : El (type919 _83123)) : Prf (term0 _83123 P) ≔ λ x : El _83123, (@lem3184696 _83123 P x);
opaque symbol lem3184729 [_83123] : Prf (term1 _83123) ≔ λ P : El (type919 _83123), (@lem3184724 _83123 P);
