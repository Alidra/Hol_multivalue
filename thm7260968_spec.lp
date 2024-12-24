require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7260968 [_137613] (f : El (fun _137613 real)) (s : El (fun _137613 bool)) (g : El (fun _137613 real)) : Prf (⇒ (∀ (λ x : El _137613, (⇒ ((@IN _137613) x s) (= ((λ i : El _137613, (f i)) x) (g x))))) (= ((@sum _137613) s (λ i : El _137613, (f i))) ((@sum _137613) s g)));
