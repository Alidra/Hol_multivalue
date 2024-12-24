require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3471961 [_90037] : Prf (∀ (λ u : El (fun _90037 bool), (∀ (λ s : El (fun (fun _90037 bool) bool), (= ((@DIFF _90037) u ((@INTERS _90037) s)) ((@UNIONS _90037) ((@GSPEC (fun _90037 bool)) (λ GEN_PVAR_64 : El (fun _90037 bool), (∃ (λ t : El (fun _90037 bool), ((@SETSPEC (fun _90037 bool)) GEN_PVAR_64 ((@IN (fun _90037 bool)) t s) ((@DIFF _90037) u t))))))))))));
