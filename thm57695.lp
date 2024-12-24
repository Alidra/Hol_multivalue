require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm57695_term_abbrevs;
opaque symbol lem57695 [A] (t : El A) : Prf (= (term0 A t) (= ((@LET_END A) t) t)) ≔ REFL (term0 A t);
