require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3386920 [_87967 _87968] (P : El (fun _87967 bool)) : Prf (∀ (λ f : El (fun _87968 _87967), (∀ (λ s : El (fun _87968 bool), (= (∀ (λ y : El _87967, (⇒ ((@IN _87967) y ((@IMAGE _87968 _87967) f s)) (P y)))) (∀ (λ x : El _87968, (⇒ ((@IN _87968) x s) (P (f x))))))))));
