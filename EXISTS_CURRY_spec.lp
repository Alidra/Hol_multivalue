require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem53650 [_5431 _5437 _5438] : Prf (∀ (λ P : El (fun (fun (prod _5438 _5437) _5431) bool), (= (∃ (λ f : El (fun (prod _5438 _5437) _5431), (P f))) (∃ (λ f : El (fun _5438 (fun _5437 _5431)), (P ((@GABS (fun (prod _5438 _5437) _5431)) (λ f' : El (fun (prod _5438 _5437) _5431), (∀ (λ a : El _5438, (∀ (λ b : El _5437, ((@GEQ _5431) (f' ((@̦‚ _5438 _5437) a b)) (f a b))))))))))))));
