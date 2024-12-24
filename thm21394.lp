require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm21394_term_abbrevs;
opaque symbol lem21394 (a : El bool) (b : El bool) : Prf (= (= (⇒ a b) (term0 a b)) (= (⇒ a b) (term0 a b))) ≔ REFL (= (⇒ a b) (term0 a b));
