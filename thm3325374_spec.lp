require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3325374 [_86841] (s : El (fun _86841 bool)) (u : El (fun (fun _86841 bool) bool)) : Prf (∀ (λ x : El _86841, (= ((@IN _86841) x ((@UNIONS _86841) ((@INSERT (fun _86841 bool)) s u))) ((@IN _86841) x ((@UNION _86841) s ((@UNIONS _86841) u))))));
