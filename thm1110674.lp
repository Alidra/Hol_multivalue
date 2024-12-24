require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1110672_spec;
require open hol-light.thm1110673_spec;
opaque symbol lem1110674 [A] (r : El (type1402 A)) : Prf (= ((@PAIRWISE A) r (@NIL A)) T) ≔ EQ_MP (@lem1110673 A r) (@lem1110672 A r);
