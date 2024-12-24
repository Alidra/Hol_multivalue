require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1099518_term_abbrevs;
opaque symbol lem1099518 [_25272] (n : El num) (x : El _25272) : Prf (= (term0 _25272 n x) (= (term1 _25272 n x) (term2 _25272 n x))) ≔ REFL (term0 _25272 n x);
