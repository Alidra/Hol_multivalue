require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.HD_term_abbrevs;
require open hol-light.thm1094865_spec;
require open hol-light.thm1094866_spec;
opaque symbol lem1094867 [A] (t : El (list A)) (h : El A) : Prf (= (term0 A h t) h) ≔ EQ_MP (@lem1094866 A t h) (@lem1094865 A t h);
