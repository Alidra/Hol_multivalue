require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1109866 [_25786 _25787] : Prf (∧ (∀ (λ f : El (fun _25787 (fun _25786 bool)), (∀ (λ l : El (list _25786), (= ((@ALLPAIRS _25786 _25787) f (@NIL _25787) l) T))))) (∀ (λ h : El _25787, (∀ (λ f : El (fun _25787 (fun _25786 bool)), (∀ (λ t : El (list _25787), (∀ (λ l : El (list _25786), (= ((@ALLPAIRS _25786 _25787) f ((@CONS _25787) h t) l) (∧ ((@ALL _25786) (f h) l) ((@ALLPAIRS _25786 _25787) f t l))))))))))));
