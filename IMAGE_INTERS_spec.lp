require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3470554 [_89991 _90000] : Prf (∀ (λ f : El (fun _89991 _90000), (∀ (λ s : El (fun (fun _89991 bool) bool), (⇒ (∧ (¬ (= s (@EMPTY (fun _89991 bool)))) (∀ (λ x : El _89991, (∀ (λ y : El _89991, (⇒ (∧ ((@IN _89991) x ((@UNIONS _89991) s)) (∧ ((@IN _89991) y ((@UNIONS _89991) s)) (= (f x) (f y)))) (= x y))))))) (= ((@IMAGE _89991 _90000) f ((@INTERS _89991) s)) ((@INTERS _90000) ((@IMAGE (fun _89991 bool) (fun _90000 bool)) ((@IMAGE _89991 _90000) f) s))))))));
