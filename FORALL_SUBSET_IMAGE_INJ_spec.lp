require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3655850 [_93578 _93585] : Prf (∀ (λ P : El (fun (fun _93585 bool) bool), (∀ (λ f : El (fun _93578 _93585), (∀ (λ s : El (fun _93578 bool), (= (∀ (λ t : El (fun _93585 bool), (⇒ ((@SUBSET _93585) t ((@IMAGE _93578 _93585) f s)) (P t)))) (∀ (λ t : El (fun _93578 bool), (⇒ (∧ ((@SUBSET _93578) t s) (∀ (λ x : El _93578, (∀ (λ y : El _93578, (⇒ (∧ ((@IN _93578) x t) ((@IN _93578) y t)) (= (= (f x) (f y)) (= x y)))))))) (P ((@IMAGE _93578 _93585) f t))))))))))));
