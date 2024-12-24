require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3839332 [_99546 _99547] : Prf (∀ (λ s : El (fun _99546 bool), (∀ (λ f : El (fun _99546 (fun _99547 _99547)), (∀ (λ g : El (fun _99546 (fun _99547 _99547)), (∀ (λ b : El _99547, (⇒ (∧ ((@FINITE _99546) s) (∧ (∀ (λ x : El _99546, (⇒ ((@IN _99546) x s) (= (f x) (g x))))) (∧ (∀ (λ x : El _99546, (∀ (λ y : El _99546, (∀ (λ s' : El _99547, (⇒ (¬ (= x y)) (= (f x (f y s')) (f y (f x s')))))))))) (∀ (λ x : El _99546, (∀ (λ y : El _99546, (∀ (λ s' : El _99547, (⇒ (¬ (= x y)) (= (g x (g y s')) (g y (g x s'))))))))))))) (= ((@ITSET _99547 _99546) f s b) ((@ITSET _99547 _99546) g s b)))))))))));
