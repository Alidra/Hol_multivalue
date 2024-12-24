require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4339138 [_104190 _104196] : Prf (∀ (λ s : El (fun _104190 bool), (∀ (λ t : El (fun _104196 bool), (∀ (λ s' : El (fun _104190 bool), (∀ (λ t' : El (fun _104196 bool), (= ((@SUBSET (prod _104190 _104196)) ((@CROSS _104196 _104190) s t) ((@CROSS _104196 _104190) s' t')) (∨ (= s (@EMPTY _104190)) (∨ (= t (@EMPTY _104196)) (∧ ((@SUBSET _104190) s s') ((@SUBSET _104196) t t')))))))))))));
