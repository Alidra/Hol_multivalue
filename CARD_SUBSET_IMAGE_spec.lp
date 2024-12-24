require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4018621 [_101783 _101790] : Prf (∀ (λ f : El (fun _101783 _101790), (∀ (λ s : El (fun _101790 bool), (∀ (λ t : El (fun _101783 bool), (⇒ (∧ ((@FINITE _101783) t) ((@SUBSET _101790) s ((@IMAGE _101783 _101790) f t))) (<= ((@CARD _101790) s) ((@CARD _101783) t)))))))));
