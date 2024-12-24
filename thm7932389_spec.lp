require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7932389 [_88266 _88270] (f : El (fun _88270 _88266)) (s : El (fun _88270 bool)) (t : El (fun _88266 bool)) : Prf ((λ t' : El (fun _88266 bool), (⇒ (∧ (∀ (λ y : El _88266, (⇒ ((@IN _88266) y t') (∃ (λ x : El _88270, (= (f x) y)))))) (∀ (λ x : El _88270, (= ((@IN _88266) (f x) t') ((@IN _88270) x s))))) (= ((@IMAGE _88270 _88266) f s) t'))) t);
