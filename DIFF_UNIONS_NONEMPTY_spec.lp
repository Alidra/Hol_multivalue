require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3477701 [_90228] : Prf (∀ (λ u : El (fun _90228 bool), (∀ (λ s : El (fun (fun _90228 bool) bool), (⇒ (¬ (= s (@EMPTY (fun _90228 bool)))) (= ((@DIFF _90228) u ((@UNIONS _90228) s)) ((@INTERS _90228) ((@GSPEC (fun _90228 bool)) (λ GEN_PVAR_69 : El (fun _90228 bool), (∃ (λ t : El (fun _90228 bool), ((@SETSPEC (fun _90228 bool)) GEN_PVAR_69 ((@IN (fun _90228 bool)) t s) ((@DIFF _90228) u t)))))))))))));
