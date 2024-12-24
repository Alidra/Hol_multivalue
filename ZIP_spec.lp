require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1109008 [_25738 _25739 _25763 _25764] (h1' : El _25763) (h2' : El _25764) (t1 : El (list _25763)) (t2 : El (list _25764)) : Prf (∧ (= ((@ZIP _25738 _25739) (@NIL _25738) (@NIL _25739)) (@NIL (prod _25738 _25739))) (= ((@ZIP _25763 _25764) ((@CONS _25763) h1' t1) ((@CONS _25764) h2' t2)) ((@CONS (prod _25763 _25764)) ((@̦‚ _25763 _25764) h1' h2') ((@ZIP _25763 _25764) t1 t2))));
