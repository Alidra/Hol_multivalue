require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7083749 [_132408] : Prf (∀ (λ f : El (fun _132408 real), (∀ (λ s : El (fun _132408 bool), (⇒ ((@FINITE _132408) s) (real_le (real_abs ((@sum _132408) s f)) ((@sum _132408) s (λ x : El _132408, (real_abs (f x))))))))));
