require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm912743_term_abbrevs;
require open hol-light.thm709122_spec;
require open hol-light.thm709125_spec;
opaque symbol lem912743 : Prf (= term0 term1) ≔ TRANS (@lem709122) (@lem709125);
