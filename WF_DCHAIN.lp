require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.WF_DCHAIN_term_abbrevs;
require open hol-light.thm310219_spec;
require open hol-light.thm316636_spec;
opaque symbol lem316637 [A] (<< : El (type1402 A)) : Prf (= ((@WF A) <<) (term0 A <<)) ≔ EQ_MP (@lem310219 A <<) (@lem316636 A <<);
