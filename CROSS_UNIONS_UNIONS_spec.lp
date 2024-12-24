require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4372154 [_104717 _104718] : Prf (∀ (λ f : El (fun (fun _104717 bool) bool), (∀ (λ g : El (fun (fun _104718 bool) bool), (= ((@CROSS _104718 _104717) ((@UNIONS _104717) f) ((@UNIONS _104718) g)) ((@UNIONS (prod _104717 _104718)) ((@GSPEC (fun (prod _104717 _104718) bool)) (λ GEN_PVAR_131 : El (fun (prod _104717 _104718) bool), (∃ (λ s : El (fun _104717 bool), (∃ (λ t : El (fun _104718 bool), ((@SETSPEC (fun (prod _104717 _104718) bool)) GEN_PVAR_131 (∧ ((@IN (fun _104717 bool)) s f) ((@IN (fun _104718 bool)) t g)) ((@CROSS _104718 _104717) s t))))))))))))));
