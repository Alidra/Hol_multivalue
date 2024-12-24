require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7068309 [_131590] : Prf (∀ (λ f : El (fun _131590 real), (∀ (λ s : El (fun _131590 bool), (∀ (λ t : El (fun _131590 bool), (⇒ (∧ ((@FINITE _131590) s) ((@SUBSET _131590) t s)) (= ((@sum _131590) ((@DIFF _131590) s t) f) (real_sub ((@sum _131590) s f) ((@sum _131590) t f))))))))));
