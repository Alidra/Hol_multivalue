require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1108937_term_abbrevs;
require open hol-light.thm1108934_spec;
opaque symbol lem1108936 [_25719 _25727] : Prf (term0 _25719 _25727) ≔ ∧ₑ₁ (@lem1108934 _25719 _25727);
opaque symbol lem1108937 [_25719 _25727] (l2 : El (list _25727)) : Prf (term1 _25719 _25727 l2) ≔ (@lem1108936 _25719 _25727) l2;
