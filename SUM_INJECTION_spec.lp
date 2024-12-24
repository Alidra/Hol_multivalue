require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7178665 [_135209] : Prf (∀ (λ f : El (fun _135209 real), (∀ (λ p : El (fun _135209 _135209), (∀ (λ s : El (fun _135209 bool), (⇒ (∧ ((@FINITE _135209) s) (∧ (∀ (λ x : El _135209, (⇒ ((@IN _135209) x s) ((@IN _135209) (p x) s)))) (∀ (λ x : El _135209, (∀ (λ y : El _135209, (⇒ (∧ ((@IN _135209) x s) (∧ ((@IN _135209) y s) (= (p x) (p y)))) (= x y)))))))) (= ((@sum _135209) s ((@o _135209 _135209 real) f p)) ((@sum _135209) s f)))))))));
