require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm538894_term_abbrevs;
require open hol-light.thm538851_spec;
opaque symbol lem538893 : Prf term0 ≔ ∧ₑ₁ (@lem538851);
opaque symbol lem538894 (n : El num) : Prf (term1 n) ≔ (@lem538893) n;
