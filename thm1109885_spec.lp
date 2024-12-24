require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1109885 [_25786 _25787] (h : El _25787) (f : El (fun _25787 (fun _25786 bool))) (t : El (list _25787)) (l : El (list _25786)) : Prf (= ((λ l' : El (list _25786), (= ((@ALLPAIRS _25786 _25787) f ((@CONS _25787) h t) l') (∧ ((@ALL _25786) (f h) l') ((@ALLPAIRS _25786 _25787) f t l')))) l) (= ((@ALLPAIRS _25786 _25787) f ((@CONS _25787) h t) l) (∧ ((@ALL _25786) (f h) l) ((@ALLPAIRS _25786 _25787) f t l))));
