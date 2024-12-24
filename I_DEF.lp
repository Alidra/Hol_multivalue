require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.I_DEF_term_abbrevs;
opaque symbol lem15398 [A] : Prf (= (@I A) (term0 A)) ≔ @I_def A;
