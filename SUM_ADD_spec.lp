require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7068796 [_131713] : Prf (∀ (λ f : El (fun _131713 real), (∀ (λ g : El (fun _131713 real), (∀ (λ s : El (fun _131713 bool), (⇒ ((@FINITE _131713) s) (= ((@sum _131713) s (λ x : El _131713, (real_add (f x) (g x)))) (real_add ((@sum _131713) s f) ((@sum _131713) s g))))))))));
