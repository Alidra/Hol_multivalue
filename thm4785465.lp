require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm4785465_term_abbrevs;
require open hol-light.thm4785464_spec;
opaque symbol lem4785465 [A] : Prf (term0 A) ≔ ∧ₑ₂ (@lem4785464 A);
