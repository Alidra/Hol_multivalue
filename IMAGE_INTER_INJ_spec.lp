require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3373798 [_87647 _87658] : Prf (∀ (λ f : El (fun _87647 _87658), (∀ (λ s : El (fun _87647 bool), (∀ (λ t : El (fun _87647 bool), (⇒ (∀ (λ x : El _87647, (∀ (λ y : El _87647, (⇒ (= (f x) (f y)) (= x y)))))) (= ((@IMAGE _87647 _87658) f ((@INTER _87647) s t)) ((@INTER _87658) ((@IMAGE _87647 _87658) f s) ((@IMAGE _87647 _87658) f t))))))))));
