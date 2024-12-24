require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm795_term_abbrevs;
require open hol-light.thm793_spec;
require open hol-light.thm794_spec;
opaque symbol lem795 (q : El bool) (p : El bool) (r : El bool) : Prf (= (term0 p q r) (term0 q p r)) ≔ EQ_MP (@lem794 q p r) (@lem793 p q r);
