require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm2305813_term_abbrevs;
require open hol-light.REAL_MUL_AC_spec;
opaque symbol lem2305813 (n : El real) (m : El real) (p : El real) : Prf (term0 n m p) ≔ ∧ₑ₂ (@lem1486340 n m p);
