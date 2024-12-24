require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1105065 [_25498 _25501 _25508] (h1' : El _25501) (f : El (fun _25501 (fun _25508 _25498))) (t1 : El (list _25501)) (l : El (list _25508)) : Prf (= ((λ l' : El (list _25508), (= ((@MAP2 _25498 _25501 _25508) f ((@CONS _25501) h1' t1) l') ((@CONS _25498) (f h1' ((@HD _25508) l')) ((@MAP2 _25498 _25501 _25508) f t1 ((@TL _25508) l'))))) l) (= ((@MAP2 _25498 _25501 _25508) f ((@CONS _25501) h1' t1) l) ((@CONS _25498) (f h1' ((@HD _25508) l)) ((@MAP2 _25498 _25501 _25508) f t1 ((@TL _25508) l)))));
