require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1104044 [_25409 _25416] (P : El (fun _25409 (fun _25416 bool))) (l2 : El (list _25416)) : Prf (= ((λ l2' : El (list _25416), (= ((@ALL2 _25409 _25416) P (@NIL _25409) l2') (= l2' (@NIL _25416)))) l2) (= ((@ALL2 _25409 _25416) P (@NIL _25409) l2) (= l2 (@NIL _25416))));
