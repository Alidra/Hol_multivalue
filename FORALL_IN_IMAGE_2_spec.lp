require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3390936 [_88066 _88069] : Prf (∀ (λ f : El (fun _88069 _88066), (∀ (λ P : El (fun _88066 (fun _88066 bool)), (∀ (λ s : El (fun _88069 bool), (= (∀ (λ x : El _88066, (∀ (λ y : El _88066, (⇒ (∧ ((@IN _88066) x ((@IMAGE _88069 _88066) f s)) ((@IN _88066) y ((@IMAGE _88069 _88066) f s))) (P x y)))))) (∀ (λ x : El _88069, (∀ (λ y : El _88069, (⇒ (∧ ((@IN _88069) x s) ((@IN _88069) y s)) (P (f x) (f y))))))))))))));
