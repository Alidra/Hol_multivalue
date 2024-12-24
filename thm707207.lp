require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm707207_term_abbrevs;
require open hol-light.thm546243_spec;
require open hol-light.thm546265_spec;
opaque symbol lem707207 : Prf (= term0 term1) ≔ TRANS (@lem546243) (@lem546265);
