require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4380546 [_104960 _104961] : Prf (∀ (λ s : El (fun _104960 bool), (∀ (λ f : El (fun (fun _104961 bool) bool), (= ((@CROSS _104961 _104960) s ((@INTERS _104961) f)) ((@COND (fun (prod _104960 _104961) bool)) (= f (@EMPTY (fun _104961 bool))) ((@CROSS _104961 _104960) s (@UNIV _104961)) ((@INTERS (prod _104960 _104961)) ((@GSPEC (fun (prod _104960 _104961) bool)) (λ GEN_PVAR_137 : El (fun (prod _104960 _104961) bool), (∃ (λ t : El (fun _104961 bool), ((@SETSPEC (fun (prod _104960 _104961) bool)) GEN_PVAR_137 ((@IN (fun _104961 bool)) t f) ((@CROSS _104961 _104960) s t)))))))))))));
