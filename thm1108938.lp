require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1108938_term_abbrevs;
opaque symbol lem1108938 [_25719 _25727] (l2 : El (list _25727)) : Prf (= (term0 _25719 _25727 l2) (= ((@ZIP _25719 _25727) (@NIL _25719) l2) (@NIL (prod _25719 _25727)))) ≔ REFL (term0 _25719 _25727 l2);
