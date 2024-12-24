require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7123384 [_133013] : Prf (∀ (λ f : El (fun _133013 real), (∀ (λ s : El (fun _133013 bool), (∀ (λ a : El _133013, (⇒ ((@FINITE _133013) s) (= ((@sum _133013) ((@DELETE _133013) s a) f) ((@COND real) ((@IN _133013) a s) (real_sub ((@sum _133013) s f) (f a)) ((@sum _133013) s f))))))))));
