require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem51057 [_5146 _5153 _5154] (t : El (fun (prod _5154 _5153) _5146)) : Prf (= (= (λ p : El (prod _5154 _5153), (t p)) ((@GABS (fun (prod _5154 _5153) _5146)) (λ f : El (fun (prod _5154 _5153) _5146), (∀ (λ x : El _5154, (∀ (λ y : El _5153, ((@GEQ _5146) (f ((@̦‚ _5154 _5153) x y)) (t ((@̦‚ _5154 _5153) x y)))))))))) (∀ (λ p1 : El _5154, (∀ (λ p2 : El _5153, (= ((λ p : El (prod _5154 _5153), (t p)) ((@̦‚ _5154 _5153) p1 p2)) ((@GABS (fun (prod _5154 _5153) _5146)) (λ f : El (fun (prod _5154 _5153) _5146), (∀ (λ x : El _5154, (∀ (λ y : El _5153, ((@GEQ _5146) (f ((@̦‚ _5154 _5153) x y)) (t ((@̦‚ _5154 _5153) x y)))))))) ((@̦‚ _5154 _5153) p1 p2))))))));
