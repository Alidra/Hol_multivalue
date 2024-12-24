require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3647316 [_93365 _93381] : Prf (∀ (λ P : El (fun (fun _93381 bool) bool), (∀ (λ f : El (fun _93365 _93381), (∀ (λ s : El (fun _93365 bool), (= (∃ (λ t : El (fun _93381 bool), (∧ ((@SUBSET _93381) t ((@IMAGE _93365 _93381) f s)) (P t)))) (∃ (λ t : El (fun _93365 bool), (∧ ((@SUBSET _93365) t s) (P ((@IMAGE _93365 _93381) f t))))))))))));
