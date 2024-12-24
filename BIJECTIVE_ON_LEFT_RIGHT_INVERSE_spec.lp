require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3570865 [_91535 _91536] : Prf (∀ (λ f : El (fun _91536 _91535), (∀ (λ s : El (fun _91536 bool), (∀ (λ t : El (fun _91535 bool), (⇒ (∀ (λ x : El _91536, (⇒ ((@IN _91536) x s) ((@IN _91535) (f x) t)))) (= (∧ (∀ (λ x : El _91536, (∀ (λ y : El _91536, (⇒ (∧ ((@IN _91536) x s) (∧ ((@IN _91536) y s) (= (f x) (f y)))) (= x y)))))) (∀ (λ y : El _91535, (⇒ ((@IN _91535) y t) (∃ (λ x : El _91536, (∧ ((@IN _91536) x s) (= (f x) y)))))))) (∃ (λ g : El (fun _91535 _91536), (∧ (∀ (λ y : El _91535, (⇒ ((@IN _91535) y t) ((@IN _91536) (g y) s)))) (∧ (∀ (λ y : El _91535, (⇒ ((@IN _91535) y t) (= (f (g y)) y)))) (∀ (λ x : El _91536, (⇒ ((@IN _91536) x s) (= (g (f x)) x))))))))))))))));
