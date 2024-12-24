require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4360794 [_104453 _104454 _104486 _104487] : Prf (∧ (∀ (λ s : El (fun _104453 bool), (∀ (λ t : El (fun _104454 bool), (∀ (λ u : El (fun _104454 bool), (= ((@CROSS _104454 _104453) s ((@INTER _104454) t u)) ((@INTER (prod _104453 _104454)) ((@CROSS _104454 _104453) s t) ((@CROSS _104454 _104453) s u))))))))) (∀ (λ s : El (fun _104486 bool), (∀ (λ t : El (fun _104486 bool), (∀ (λ u : El (fun _104487 bool), (= ((@CROSS _104487 _104486) ((@INTER _104486) s t) u) ((@INTER (prod _104486 _104487)) ((@CROSS _104487 _104486) s u) ((@CROSS _104487 _104486) t u))))))))));
