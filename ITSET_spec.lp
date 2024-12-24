require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3815973 [_99240 _99241] : Prf (∀ (λ b : El _99240, (∀ (λ f : El (fun _99241 (fun _99240 _99240)), (∀ (λ s : El (fun _99241 bool), (= ((@ITSET _99240 _99241) f s b) ((@ε (fun (fun _99241 bool) _99240)) (λ g : El (fun (fun _99241 bool) _99240), (∧ (= (g (@EMPTY _99241)) b) (∀ (λ x : El _99241, (∀ (λ s' : El (fun _99241 bool), (⇒ ((@FINITE _99241) s') (= (g ((@INSERT _99241) x s')) ((@COND _99240) ((@IN _99241) x s') (g s') (f x (g s'))))))))))) s))))))));
