require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1105741_term_abbrevs;
require open hol-light.thm1105738_spec;
opaque symbol lem1105740 [_25569] : Prf (term0 _25569) ≔ ∧ₑ₁ (@lem1105738 _25569);
opaque symbol lem1105741 [_25569] (l : El (list _25569)) : Prf (term1 _25569 l) ≔ (@lem1105740 _25569) l;
