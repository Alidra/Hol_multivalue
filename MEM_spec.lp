require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1103203 [_25376] (h : El _25376) (x : El _25376) (t : El (list _25376)) : Prf (∧ (= ((@MEM _25376) x (@NIL _25376)) F) (= ((@MEM _25376) x ((@CONS _25376) h t)) (∨ (= x h) ((@MEM _25376) x t))));
