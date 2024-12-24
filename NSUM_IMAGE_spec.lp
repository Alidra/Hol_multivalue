require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem6961680 [_127560 _127584] : Prf (∀ (λ f : El (fun _127584 _127560), (∀ (λ g : El (fun _127560 num), (∀ (λ s : El (fun _127584 bool), (⇒ (∀ (λ x : El _127584, (∀ (λ y : El _127584, (⇒ (∧ ((@IN _127584) x s) (∧ ((@IN _127584) y s) (= (f x) (f y)))) (= x y)))))) (= ((@nsum _127560) ((@IMAGE _127584 _127560) f s) g) ((@nsum _127584) s ((@o _127584 _127560 num) g f))))))))));
