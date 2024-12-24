require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1107273 [_25617 _25623] (h : El (prod _25623 _25617)) (a : El _25623) (t : El (list (prod _25623 _25617))) : Prf (= ((λ t' : El (list (prod _25623 _25617)), (= ((@ASSOC _25617 _25623) a ((@CONS (prod _25623 _25617)) h t')) ((@COND _25617) (= ((@FST _25623 _25617) h) a) ((@SND _25623 _25617) h) ((@ASSOC _25617 _25623) a t')))) t) (= ((@ASSOC _25617 _25623) a ((@CONS (prod _25623 _25617)) h t)) ((@COND _25617) (= ((@FST _25623 _25617) h) a) ((@SND _25623 _25617) h) ((@ASSOC _25617 _25623) a t))));
