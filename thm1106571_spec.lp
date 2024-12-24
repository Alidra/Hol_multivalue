require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1106571 [_25594] (h : El _25594) (P : El (fun _25594 bool)) (t : El (list _25594)) : Prf ((λ t' : El (list _25594), (= ((@FILTER _25594) P ((@CONS _25594) h t')) ((@COND (list _25594)) (P h) ((@CONS _25594) h ((@FILTER _25594) P t')) ((@FILTER _25594) P t')))) t);
