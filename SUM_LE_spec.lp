require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7071845 [_132081] : Prf (∀ (λ f : El (fun _132081 real), (∀ (λ g : El (fun _132081 real), (∀ (λ s : El (fun _132081 bool), (⇒ (∧ ((@FINITE _132081) s) (∀ (λ x : El _132081, (⇒ ((@IN _132081) x s) (real_le (f x) (g x)))))) (real_le ((@sum _132081) s f) ((@sum _132081) s g)))))))));
