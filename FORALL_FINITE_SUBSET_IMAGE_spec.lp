require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3694570 [_93870 _93890] : Prf (∀ (λ P : El (fun (fun _93890 bool) bool), (∀ (λ f : El (fun _93870 _93890), (∀ (λ s : El (fun _93870 bool), (= (∀ (λ t : El (fun _93890 bool), (⇒ (∧ ((@FINITE _93890) t) ((@SUBSET _93890) t ((@IMAGE _93870 _93890) f s))) (P t)))) (∀ (λ t : El (fun _93870 bool), (⇒ (∧ ((@FINITE _93870) t) ((@SUBSET _93870) t s)) (P ((@IMAGE _93870 _93890) f t))))))))))));
