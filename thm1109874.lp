require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1109872_spec;
require open hol-light.thm1109873_spec;
opaque symbol lem1109874 [_25786 _25787] (f : El (type1470 _25786 _25787)) (l : El (list _25786)) : Prf (= ((@ALLPAIRS _25786 _25787) f (@NIL _25787) l) T) ≔ EQ_MP (@lem1109873 _25786 _25787 f l) (@lem1109872 _25786 _25787 f l);
