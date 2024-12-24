require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.ASSOC_term_abbrevs;
require open hol-light.thm1107272_spec;
require open hol-light.thm1107273_spec;
opaque symbol lem1107274 [_25617 _25623] (h : El (prod _25623 _25617)) (a : El _25623) (t : El (type1641 _25617 _25623)) : Prf (= (term0 _25617 _25623 a h t) (term1 _25617 _25623 h a t)) ≔ EQ_MP (@lem1107273 _25617 _25623 h a t) (@lem1107272 _25617 _25623 h a t);
