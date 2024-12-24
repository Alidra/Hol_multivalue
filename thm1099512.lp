require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1099512_term_abbrevs;
opaque symbol lem1099512 [_25272] (x : El _25272) : Prf (= (term0 _25272 x) (= (term1 _25272 x) (@NIL _25272))) ≔ REFL (term0 _25272 x);
