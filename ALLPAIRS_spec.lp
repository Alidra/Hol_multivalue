require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1109887 [_25786 _25787] (h : El _25787) (f : El (fun _25787 (fun _25786 bool))) (t : El (list _25787)) (l : El (list _25786)) : Prf (∧ (= ((@ALLPAIRS _25786 _25787) f (@NIL _25787) l) T) (= ((@ALLPAIRS _25786 _25787) f ((@CONS _25787) h t) l) (∧ ((@ALL _25786) (f h) l) ((@ALLPAIRS _25786 _25787) f t l))));
