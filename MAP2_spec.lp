require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1105126 [_25542 _25543 _25549] (h1' : El _25543) (h2' : El _25542) (f : El (fun _25543 (fun _25542 _25549))) (t1 : El (list _25543)) (t2 : El (list _25542)) : Prf (∧ (= ((@MAP2 _25549 _25543 _25542) f (@NIL _25543) (@NIL _25542)) (@NIL _25549)) (= ((@MAP2 _25549 _25543 _25542) f ((@CONS _25543) h1' t1) ((@CONS _25542) h2' t2)) ((@CONS _25549) (f h1' h2') ((@MAP2 _25549 _25543 _25542) f t1 t2))));
