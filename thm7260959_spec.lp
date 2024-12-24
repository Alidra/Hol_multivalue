require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7260959 [_132349] (f : El (fun _132349 real)) (s : El (fun _132349 bool)) (g : El (fun _132349 real)) : Prf ((λ g' : El (fun _132349 real), (⇒ (∀ (λ x : El _132349, (⇒ ((@IN _132349) x s) (= (f x) (g' x))))) (= ((@sum _132349) s f) ((@sum _132349) s g')))) g);
