require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7122619 [_132960] : Prf (∀ (λ f : El (fun _132960 real), (∀ (λ s : El (fun _132960 bool), (∀ (λ a : El _132960, (⇒ (∧ ((@FINITE _132960) s) ((@IN _132960) a s)) (= ((@sum _132960) ((@DELETE _132960) s a) f) (real_sub ((@sum _132960) s f) (f a))))))))));
