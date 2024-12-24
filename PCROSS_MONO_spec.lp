require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem8010834 [_142122 _142123 _142124] : Prf (∀ (λ s : El (fun (cart _142122 _142123) bool), (∀ (λ t : El (fun (cart _142122 _142124) bool), (∀ (λ s' : El (fun (cart _142122 _142123) bool), (∀ (λ t' : El (fun (cart _142122 _142124) bool), (⇒ (∧ ((@SUBSET (cart _142122 _142123)) s s') ((@SUBSET (cart _142122 _142124)) t t')) ((@SUBSET (cart _142122 (finite_sum _142123 _142124))) ((@PCROSS _142122 _142123 _142124) s t) ((@PCROSS _142122 _142123 _142124) s' t')))))))))));
