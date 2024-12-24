require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm707079_term_abbrevs;
require open hol-light.thm538319_spec;
require open hol-light.thm538330_spec;
opaque symbol lem707079 : Prf (= term0 term1) ≔ TRANS (@lem538319) (@lem538330);
