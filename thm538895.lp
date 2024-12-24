require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm538895_term_abbrevs;
opaque symbol lem538895 (n : El num) : Prf (= (term0 n) (= (term1 n) (BIT1 n))) ≔ REFL (term0 n);
