require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm48220_term_abbrevs;
opaque symbol lem48220 [A B] (y : El B) (x : El A) : Prf (= (term0 A B x y) (= (term1 A B x y) x)) ≔ REFL (term0 A B x y);
