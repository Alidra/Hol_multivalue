require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5128794 [_115054 _115057] : Prf (∀ (λ s : El (fun _115054 bool), (∀ (λ t : El (fun _115057 bool), (= ((@<=_c _115057 _115054) s t) (∃ (λ g : El (fun _115057 _115054), (∀ (λ x : El _115054, (⇒ ((@IN _115054) x s) (∃ (λ y : El _115057, (∧ ((@IN _115057) y t) (= (g y) x))))))))))))));
