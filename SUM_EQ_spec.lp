require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7081239 [_132349] : Prf (∀ (λ f : El (fun _132349 real), (∀ (λ g : El (fun _132349 real), (∀ (λ s : El (fun _132349 bool), (⇒ (∀ (λ x : El _132349, (⇒ ((@IN _132349) x s) (= (f x) (g x))))) (= ((@sum _132349) s f) ((@sum _132349) s g)))))))));
