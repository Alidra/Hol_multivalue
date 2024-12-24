require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7071000 [_132039] : Prf (∀ (λ f : El (fun _132039 real), (∀ (λ g : El (fun _132039 real), (∀ (λ s : El (fun _132039 bool), (⇒ ((@FINITE _132039) s) (= ((@sum _132039) s (λ x : El _132039, (real_sub (f x) (g x)))) (real_sub ((@sum _132039) s f) ((@sum _132039) s g))))))))));
