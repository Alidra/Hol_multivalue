require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem53824 [_5456 _5462 _5463] : Prf (∀ (λ P : El (fun (fun (prod _5463 _5462) _5456) bool), (= (∀ (λ f : El (fun (prod _5463 _5462) _5456), (P f))) (∀ (λ f : El (fun _5463 (fun _5462 _5456)), (P ((@GABS (fun (prod _5463 _5462) _5456)) (λ f' : El (fun (prod _5463 _5462) _5456), (∀ (λ a : El _5463, (∀ (λ b : El _5462, ((@GEQ _5456) (f' ((@̦‚ _5463 _5462) a b)) (f a b))))))))))))));
