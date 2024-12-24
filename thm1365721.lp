require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1365721_term_abbrevs;
require open hol-light.thm1365720_spec;
opaque symbol lem1365721 (m : El num) (n : El num) : Prf (term0 m n) ≔ ∧ₑ₂ (@lem1365720 m n);
