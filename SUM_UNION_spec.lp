require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7067826 [_131550] : Prf (∀ (λ f : El (fun _131550 real), (∀ (λ s : El (fun _131550 bool), (∀ (λ t : El (fun _131550 bool), (⇒ (∧ ((@FINITE _131550) s) (∧ ((@FINITE _131550) t) ((@DISJOINT _131550) s t))) (= ((@sum _131550) ((@UNION _131550) s t) f) (real_add ((@sum _131550) s f) ((@sum _131550) t f))))))))));
