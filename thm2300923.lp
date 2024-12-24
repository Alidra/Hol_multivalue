require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm2300923_term_abbrevs;
require open hol-light.REAL_ADD_AC_spec;
opaque symbol lem2300923 (n : El real) (m : El real) (p : El real) : Prf (term0 n m p) ≔ ∧ₑ₂ (@lem1352530 n m p);
