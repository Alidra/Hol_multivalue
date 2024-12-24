require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1104037 [_25409 _25416] : Prf (∧ (∀ (λ P : El (fun _25409 (fun _25416 bool)), (∀ (λ l2 : El (list _25416), (= ((@ALL2 _25409 _25416) P (@NIL _25409) l2) (= l2 (@NIL _25416))))))) (∀ (λ h1' : El _25409, (∀ (λ P : El (fun _25409 (fun _25416 bool)), (∀ (λ t1 : El (list _25409), (∀ (λ l2 : El (list _25416), (= ((@ALL2 _25409 _25416) P ((@CONS _25409) h1' t1) l2) ((@COND bool) (= l2 (@NIL _25416)) F (∧ (P h1' ((@HD _25416) l2)) ((@ALL2 _25409 _25416) P t1 ((@TL _25416) l2))))))))))))));
