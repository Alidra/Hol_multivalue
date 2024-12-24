require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3693974 [_93804 _93824] : Prf (∀ (λ P : El (fun (fun _93824 bool) bool), (∀ (λ f : El (fun _93804 _93824), (∀ (λ s : El (fun _93804 bool), (= (∃ (λ t : El (fun _93824 bool), (∧ ((@FINITE _93824) t) (∧ ((@SUBSET _93824) t ((@IMAGE _93804 _93824) f s)) (P t))))) (∃ (λ t : El (fun _93804 bool), (∧ ((@FINITE _93804) t) (∧ ((@SUBSET _93804) t s) (P ((@IMAGE _93804 _93824) f t)))))))))))));
