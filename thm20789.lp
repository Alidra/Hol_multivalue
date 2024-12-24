require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm20789_term_abbrevs;
opaque symbol lem20789 (a : El bool) (b : El bool) : Prf (= (= (term0 a b) (term1 a b)) (= (term0 a b) (term1 a b))) ≔ REFL (= (term0 a b) (term1 a b));
