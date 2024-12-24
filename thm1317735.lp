require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1317735_term_abbrevs;
opaque symbol lem1317735 (a : El hreal) : Prf (= (term0 a) a) ≔ @axiom_21 a;
