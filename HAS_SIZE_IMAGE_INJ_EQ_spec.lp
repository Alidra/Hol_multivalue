require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4019198 [_101850 _101855] : Prf (∀ (λ f : El (fun _101855 _101850), (∀ (λ s : El (fun _101855 bool), (∀ (λ n : El num, (⇒ (∀ (λ x : El _101855, (∀ (λ y : El _101855, (⇒ (∧ ((@IN _101855) x s) (∧ ((@IN _101855) y s) (= (f x) (f y)))) (= x y)))))) (= ((@HAS_SIZE _101850) ((@IMAGE _101855 _101850) f s) n) ((@HAS_SIZE _101855) s n)))))))));
