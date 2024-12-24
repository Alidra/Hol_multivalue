require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4361537 [_104522 _104523 _104555 _104556] : Prf (∧ (∀ (λ s : El (fun _104522 bool), (∀ (λ t : El (fun _104523 bool), (∀ (λ u : El (fun _104523 bool), (= ((@CROSS _104523 _104522) s ((@UNION _104523) t u)) ((@UNION (prod _104522 _104523)) ((@CROSS _104523 _104522) s t) ((@CROSS _104523 _104522) s u))))))))) (∀ (λ s : El (fun _104555 bool), (∀ (λ t : El (fun _104555 bool), (∀ (λ u : El (fun _104556 bool), (= ((@CROSS _104556 _104555) ((@UNION _104555) s t) u) ((@UNION (prod _104555 _104556)) ((@CROSS _104556 _104555) s u) ((@CROSS _104556 _104555) t u))))))))));
