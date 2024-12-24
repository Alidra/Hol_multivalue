require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.WF_IND_term_abbrevs;
require open hol-light.thm307612_spec;
require open hol-light.thm309905_spec;
opaque symbol lem309906 [A] (<< : El (type1402 A)) : Prf (= ((@WF A) <<) (term0 A <<)) ≔ EQ_MP (@lem307612 A <<) (@lem309905 A <<);
