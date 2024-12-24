require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4968423 [_113204] : Prf (∀ (λ s : El (fun _113204 bool), (∀ (λ f : El (fun _113204 _113204), (⇒ (∧ ((@FINITE _113204) s) (= ((@IMAGE _113204 _113204) f s) s)) (∀ (λ x : El _113204, (∀ (λ y : El _113204, (⇒ (∧ ((@IN _113204) x s) (∧ ((@IN _113204) y s) (= (f x) (f y)))) (= x y)))))))))));
