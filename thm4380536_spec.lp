require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4380536 [_105011 _105012] : Prf (∀ (λ f : El (fun (fun _105011 bool) bool), (∀ (λ t : El (fun _105012 bool), (= ((@CROSS _105012 _105011) ((@INTERS _105011) f) t) ((@COND (fun (prod _105011 _105012) bool)) (= f (@EMPTY (fun _105011 bool))) ((@CROSS _105012 _105011) (@UNIV _105011) t) ((@INTERS (prod _105011 _105012)) ((@GSPEC (fun (prod _105011 _105012) bool)) (λ GEN_PVAR_138 : El (fun (prod _105011 _105012) bool), (∃ (λ s : El (fun _105011 bool), ((@SETSPEC (fun (prod _105011 _105012) bool)) GEN_PVAR_138 ((@IN (fun _105011 bool)) s f) ((@CROSS _105012 _105011) s t)))))))))))));
