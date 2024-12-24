require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1103201 [_25376] (h : El _25376) (x : El _25376) (t : El (list _25376)) : Prf (= ((λ t' : El (list _25376), (= ((@MEM _25376) x ((@CONS _25376) h t')) (∨ (= x h) ((@MEM _25376) x t')))) t) (= ((@MEM _25376) x ((@CONS _25376) h t)) (∨ (= x h) ((@MEM _25376) x t))));
