require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7261377 [_137613] (s : El (fun _137613 bool)) (f : El (fun _137613 real)) (g : El (fun _137613 real)) (h1 : Prf (∀ (λ x : El _137613, (⇒ ((@IN _137613) x s) (= (f x) (g x)))))) : Prf (= ((@sum _137613) s (λ i : El _137613, (f i))) ((@sum _137613) s g));
