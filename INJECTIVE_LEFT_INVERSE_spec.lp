require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3576367 [_91597 _91600] (f : El (fun _91597 _91600)) : Prf (= (∀ (λ x : El _91597, (∀ (λ y : El _91597, (⇒ (= (f x) (f y)) (= x y)))))) (∃ (λ g : El (fun _91600 _91597), (∀ (λ x : El _91597, (= (g (f x)) x))))));
