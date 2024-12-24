require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3689549 [_93766 _93773] : Prf (∀ (λ P : El (fun (fun _93773 bool) bool), (∀ (λ f : El (fun _93766 _93773), (∀ (λ s : El (fun _93766 bool), (= (∀ (λ t : El (fun _93773 bool), (⇒ (∧ ((@FINITE _93773) t) ((@SUBSET _93773) t ((@IMAGE _93766 _93773) f s))) (P t)))) (∀ (λ t : El (fun _93766 bool), (⇒ (∧ ((@FINITE _93766) t) (∧ ((@SUBSET _93766) t s) (∀ (λ x : El _93766, (∀ (λ y : El _93766, (⇒ (∧ ((@IN _93766) x t) ((@IN _93766) y t)) (= (= (f x) (f y)) (= x y))))))))) (P ((@IMAGE _93766 _93773) f t))))))))))));
