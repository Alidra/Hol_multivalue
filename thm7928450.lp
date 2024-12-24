require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm7928450_term_abbrevs;
opaque symbol lem7928450 [A] (r : El (type1675 A)) : Prf (= (term0 A r) (= (term1 A r) r)) ≔ @axiom_40 A r;
