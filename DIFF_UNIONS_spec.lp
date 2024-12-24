require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3476157 [_90184] : Prf (∀ (λ u : El (fun _90184 bool), (∀ (λ s : El (fun (fun _90184 bool) bool), (= ((@DIFF _90184) u ((@UNIONS _90184) s)) ((@INTER _90184) u ((@INTERS _90184) ((@GSPEC (fun _90184 bool)) (λ GEN_PVAR_68 : El (fun _90184 bool), (∃ (λ t : El (fun _90184 bool), ((@SETSPEC (fun _90184 bool)) GEN_PVAR_68 ((@IN (fun _90184 bool)) t s) ((@DIFF _90184) u t)))))))))))));
