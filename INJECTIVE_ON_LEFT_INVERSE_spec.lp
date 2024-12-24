require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3566182 [_91401 _91404] : Prf (∀ (λ f : El (fun _91401 _91404), (∀ (λ s : El (fun _91401 bool), (= (∀ (λ x : El _91401, (∀ (λ y : El _91401, (⇒ (∧ ((@IN _91401) x s) (∧ ((@IN _91401) y s) (= (f x) (f y)))) (= x y)))))) (∃ (λ g : El (fun _91404 _91401), (∀ (λ x : El _91401, (⇒ ((@IN _91401) x s) (= (g (f x)) x)))))))))));
