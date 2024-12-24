require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3388254 [_88003 _88004] (P : El (fun _88003 bool)) : Prf (∀ (λ f : El (fun _88004 _88003), (∀ (λ s : El (fun _88004 bool), (= (∃ (λ y : El _88003, (∧ ((@IN _88003) y ((@IMAGE _88004 _88003) f s)) (P y)))) (∃ (λ x : El _88004, (∧ ((@IN _88004) x s) (P (f x))))))))));
