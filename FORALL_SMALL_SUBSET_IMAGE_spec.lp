require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4075307 [_102373 _102400] : Prf (∀ (λ P : El (fun (fun _102400 bool) bool), (∀ (λ f : El (fun _102373 _102400), (∀ (λ s : El (fun _102373 bool), (∀ (λ n : El num, (= (∀ (λ t : El (fun _102400 bool), (⇒ (∧ ((@FINITE _102400) t) (∧ (< ((@CARD _102400) t) n) ((@SUBSET _102400) t ((@IMAGE _102373 _102400) f s)))) (P t)))) (∀ (λ t : El (fun _102373 bool), (⇒ (∧ ((@FINITE _102373) t) (∧ (< ((@CARD _102373) t) n) ((@SUBSET _102373) t s))) (P ((@IMAGE _102373 _102400) f t))))))))))))));
