require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1104212 [_25470 _25471] (h1' : El _25471) (h2' : El _25470) (P : El (fun _25471 (fun _25470 bool))) (t1 : El (list _25471)) (t2 : El (list _25470)) : Prf (∧ (= ((@ALL2 _25471 _25470) P (@NIL _25471) (@NIL _25470)) T) (∧ (= ((@ALL2 _25471 _25470) P ((@CONS _25471) h1' t1) (@NIL _25470)) F) (∧ (= ((@ALL2 _25471 _25470) P (@NIL _25471) ((@CONS _25470) h2' t2)) F) (= ((@ALL2 _25471 _25470) P ((@CONS _25471) h1' t1) ((@CONS _25470) h2' t2)) (∧ (P h1' h2') ((@ALL2 _25471 _25470) P t1 t2))))));
