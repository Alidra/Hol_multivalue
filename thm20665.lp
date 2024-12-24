require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm20665_term_abbrevs;
opaque symbol lem20665 [A] (x : El A) : Prf (= (term0 A x) (= (= x x) T)) ≔ REFL (term0 A x);
