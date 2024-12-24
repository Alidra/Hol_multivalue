require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1108228 [_25645 _25647 _25655] (h1' : El _25647) (f : El (fun _25647 (fun _25655 (fun _25645 _25645)))) (t1 : El (list _25647)) (l2 : El (list _25655)) (b : El _25645) : Prf ((λ b' : El _25645, (= ((@ITLIST2 _25645 _25647 _25655) f ((@CONS _25647) h1' t1) l2 b') (f h1' ((@HD _25655) l2) ((@ITLIST2 _25645 _25647 _25655) f t1 ((@TL _25655) l2) b')))) b);
