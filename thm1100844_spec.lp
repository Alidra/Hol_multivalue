require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1100844 [_25307] (h : El _25307) (P : El (fun _25307 bool)) (t : El (list _25307)) : Prf (= ((λ t' : El (list _25307), (= ((@ALL _25307) P ((@CONS _25307) h t')) (∧ (P h) ((@ALL _25307) P t')))) t) (= ((@ALL _25307) P ((@CONS _25307) h t)) (∧ (P h) ((@ALL _25307) P t))));
