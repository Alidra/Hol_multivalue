require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4074677 [_102289 _102316] : Prf (∀ (λ P : El (fun (fun _102316 bool) bool), (∀ (λ f : El (fun _102289 _102316), (∀ (λ s : El (fun _102289 bool), (∀ (λ n : El num, (= (∃ (λ t : El (fun _102316 bool), (∧ ((@FINITE _102316) t) (∧ (< ((@CARD _102316) t) n) (∧ ((@SUBSET _102316) t ((@IMAGE _102289 _102316) f s)) (P t)))))) (∃ (λ t : El (fun _102289 bool), (∧ ((@FINITE _102289) t) (∧ (< ((@CARD _102289) t) n) (∧ ((@SUBSET _102289) t s) (P ((@IMAGE _102289 _102316) f t))))))))))))))));
