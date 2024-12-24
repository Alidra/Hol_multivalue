require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4362404 [_104591 _104592 _104624 _104625] : Prf (∧ (∀ (λ s : El (fun _104591 bool), (∀ (λ t : El (fun _104592 bool), (∀ (λ u : El (fun _104592 bool), (= ((@CROSS _104592 _104591) s ((@DIFF _104592) t u)) ((@DIFF (prod _104591 _104592)) ((@CROSS _104592 _104591) s t) ((@CROSS _104592 _104591) s u))))))))) (∀ (λ s : El (fun _104624 bool), (∀ (λ t : El (fun _104624 bool), (∀ (λ u : El (fun _104625 bool), (= ((@CROSS _104625 _104624) ((@DIFF _104624) s t) u) ((@DIFF (prod _104624 _104625)) ((@CROSS _104625 _104624) s u) ((@CROSS _104625 _104624) t u))))))))));
