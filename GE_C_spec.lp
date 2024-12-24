require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5131560 [_115095 _115098] : Prf (∀ (λ s : El (fun _115098 bool), (∀ (λ t : El (fun _115095 bool), (= ((@>=_c _115095 _115098) s t) (∃ (λ f : El (fun _115098 _115095), (∀ (λ y : El _115095, (⇒ ((@IN _115095) y t) (∃ (λ x : El _115098, (∧ ((@IN _115098) x s) (= y (f x)))))))))))))));
