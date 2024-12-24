require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm513551_term_abbrevs;
require open hol-light.ADD_AC_spec;
opaque symbol lem513551 (n : El num) (m : El num) (p : El num) : Prf (term0 n m p) ≔ ∧ₑ₂ (@lem79120 n m p);
