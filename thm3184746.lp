require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm3184746_term_abbrevs;
require open hol-light.thm3184698_spec;
opaque symbol lem3184746 [_83064] (P : El (type919 _83064)) : Prf (term0 _83064 P) ≔ λ x : El _83064, (@lem3184698 _83064 P x);
