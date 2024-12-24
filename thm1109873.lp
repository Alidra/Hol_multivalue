require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1109873_term_abbrevs;
opaque symbol lem1109873 [_25786 _25787] (f : El (type1470 _25786 _25787)) (l : El (list _25786)) : Prf (= (term0 _25786 _25787 f l) (= ((@ALLPAIRS _25786 _25787) f (@NIL _25787) l) T)) ≔ REFL (term0 _25786 _25787 f l);
