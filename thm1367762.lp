require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1367762_term_abbrevs;
require open hol-light.thm1367761_spec;
opaque symbol lem1367762 (m : El num) (n : El num) : Prf (term0 m n) ≔ ∧ₑ₂ (@lem1367761 m n);
