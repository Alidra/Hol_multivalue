require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem8010703 [_142062 _142063 _142064] : Prf (∀ (λ s : El (fun (cart _142062 _142063) bool), (∀ (λ t : El (fun (cart _142062 _142064) bool), (∀ (λ s' : El (fun (cart _142062 _142063) bool), (∀ (λ t' : El (fun (cart _142062 _142064) bool), (= ((@SUBSET (cart _142062 (finite_sum _142063 _142064))) ((@PCROSS _142062 _142063 _142064) s t) ((@PCROSS _142062 _142063 _142064) s' t')) (∨ (= s (@EMPTY (cart _142062 _142063))) (∨ (= t (@EMPTY (cart _142062 _142064))) (∧ ((@SUBSET (cart _142062 _142063)) s s') ((@SUBSET (cart _142062 _142064)) t t')))))))))))));
