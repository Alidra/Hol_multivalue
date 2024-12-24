require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm2406272_term_abbrevs;
require open hol-light.thm2406271_spec;
opaque symbol lem2406272 (m : El num) (n : El num) : Prf (term0 m n) ≔ ∧ₑ₂ (@lem2406271 m n);
