require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1108290 [_25687 _25688 _25689] (h1' : El _25689) (h2' : El _25688) (f : El (fun _25689 (fun _25688 (fun _25687 _25687)))) (t1 : El (list _25689)) (t2 : El (list _25688)) (b : El _25687) : Prf (∧ (= ((@ITLIST2 _25687 _25689 _25688) f (@NIL _25689) (@NIL _25688) b) b) (= ((@ITLIST2 _25687 _25689 _25688) f ((@CONS _25689) h1' t1) ((@CONS _25688) h2' t2) b) (f h1' h2' ((@ITLIST2 _25687 _25689 _25688) f t1 t2 b))));
