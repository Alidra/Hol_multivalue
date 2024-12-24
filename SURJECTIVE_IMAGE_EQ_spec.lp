require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3399677 [_88266 _88270] (f : El (fun _88270 _88266)) : Prf (∀ (λ s : El (fun _88270 bool), (∀ (λ t : El (fun _88266 bool), (⇒ (∧ (∀ (λ y : El _88266, (⇒ ((@IN _88266) y t) (∃ (λ x : El _88270, (= (f x) y)))))) (∀ (λ x : El _88270, (= ((@IN _88266) (f x) t) ((@IN _88270) x s))))) (= ((@IMAGE _88270 _88266) f s) t))))));
