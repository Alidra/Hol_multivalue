require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm7925131_term_abbrevs;
opaque symbol lem7925131 [A] (r : El (type1676 A)) : Prf (= (term0 A r) (= (term1 A r) r)) ≔ @axiom_38 A r;
