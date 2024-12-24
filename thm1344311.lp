require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1344311_term_abbrevs;
opaque symbol lem1344311 (x : El real) : Prf (= (term0 x) (= (term1 x) term2)) ≔ REFL (term0 x);
