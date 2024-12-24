require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7124521 [_133152 _133176] : Prf (∀ (λ f : El (fun _133176 _133152), (∀ (λ g : El (fun _133152 real), (∀ (λ s : El (fun _133176 bool), (⇒ (∀ (λ x : El _133176, (∀ (λ y : El _133176, (⇒ (∧ ((@IN _133176) x s) (∧ ((@IN _133176) y s) (= (f x) (f y)))) (= x y)))))) (= ((@sum _133152) ((@IMAGE _133176 _133152) f s) g) ((@sum _133176) s ((@o _133176 _133152 real) g f))))))))));
