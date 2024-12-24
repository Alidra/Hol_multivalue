require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1102422 [_25350 _25351] : Prf (∀ (λ h : El _25351, (∀ (λ f : El (fun _25351 (fun _25350 _25350)), (∀ (λ t : El (list _25351), (∀ (λ b : El _25350, (= ((@ITLIST _25350 _25351) f ((@CONS _25351) h t) b) (f h ((@ITLIST _25350 _25351) f t b)))))))))));
