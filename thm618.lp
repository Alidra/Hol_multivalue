require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm618_term_abbrevs;
require open hol-light.thm616_spec;
require open hol-light.thm617_spec;
opaque symbol lem618 (q : El bool) (p : El bool) (r : El bool) : Prf (= (term0 p q r) (term0 q p r)) ≔ EQ_MP (@lem617 q p r) (@lem616 p q r);
