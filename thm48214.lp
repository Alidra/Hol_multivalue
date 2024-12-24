require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm48214_term_abbrevs;
opaque symbol lem48214 [A B] (x : El A) (y : El B) : Prf (= (term0 A B x y) (= (term1 A B x y) y)) ≔ REFL (term0 A B x y);
