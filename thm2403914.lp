require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm2403914_term_abbrevs;
require open hol-light.thm2403913_spec;
opaque symbol lem2403914 (m : El num) (n : El num) : Prf (term0 m n) ≔ ∧ₑ₂ (@lem2403913 m n);
