require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1367764_term_abbrevs;
require open hol-light.thm1367762_spec;
opaque symbol lem1367764 (m : El num) (n : El num) : Prf (term0 m n) ≔ ∧ₑ₂ (@lem1367762 m n);
