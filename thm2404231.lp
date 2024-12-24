require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm2404231_term_abbrevs;
require open hol-light.thm2404230_spec;
opaque symbol lem2404231 (m : El num) (n : El num) : Prf (term0 m n) ≔ ∧ₑ₂ (@lem2404230 m n);
