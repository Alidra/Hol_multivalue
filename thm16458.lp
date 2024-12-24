require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm16458_term_abbrevs;
opaque symbol lem16458 [A] (t : El bool) : Prf (= (term0 A t) (= (term1 A t) t)) ≔ REFL (term0 A t);
