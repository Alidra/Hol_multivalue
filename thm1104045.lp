require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1104043_spec;
require open hol-light.thm1104044_spec;
opaque symbol lem1104045 [_25409 _25416] (P : El (type1413 _25409 _25416)) (l2 : El (list _25416)) : Prf (= ((@ALL2 _25409 _25416) P (@NIL _25409) l2) (= l2 (@NIL _25416))) ≔ EQ_MP (@lem1104044 _25409 _25416 P l2) (@lem1104043 _25409 _25416 P l2);
