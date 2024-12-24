require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7018470 [_129571] : Prf (∀ (λ f : El (fun _129571 num), (∀ (λ p : El (fun _129571 _129571), (∀ (λ s : El (fun _129571 bool), (⇒ (∧ ((@FINITE _129571) s) (∧ (∀ (λ x : El _129571, (⇒ ((@IN _129571) x s) ((@IN _129571) (p x) s)))) (∀ (λ x : El _129571, (∀ (λ y : El _129571, (⇒ (∧ ((@IN _129571) x s) (∧ ((@IN _129571) y s) (= (p x) (p y)))) (= x y)))))))) (= ((@nsum _129571) s ((@o _129571 _129571 num) f p)) ((@nsum _129571) s f)))))))));
