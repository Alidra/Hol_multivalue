require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm707091_term_abbrevs;
require open hol-light.thm538911_spec;
require open hol-light.thm538928_spec;
opaque symbol lem707091 : Prf (= term0 term1) ≔ TRANS (@lem538911) (@lem538928);
